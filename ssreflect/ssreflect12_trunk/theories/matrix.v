(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigops prime binomial ssralg finset groups finalg.
Require Import perm zmodp.

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
(* \matrix_(i < m) RowExpr(i) ==                                             *)
(*                   the m x n matrix with row i given by RowExpr(i) : 'rV_n *)
(*          A i j == the coefficient of matrix A : 'M_(m, n) in column j of  *)
(*                   row i, where i : 'I_m, and j : 'I_n (via the coercion   *)
(*                   fun_of_matrix : matrix >-> Funclass).                   *)
(*     const_mx a == the constant matrix whose entries are all a (dimensions *)
(*                   should be determined by context).                       *)
(*     map_mx f A == the pointwise image of A by f, i.e., the matrix Af      *)
(*                   congruent to A with Af i j = f (A i j) for all i and j. *)
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
(*   [l|r]submx A == the left/right submatrices of a row block matrix A.     *)
(*                   Note that the type of A, 'M_(m, n1 + n2) indicatres     *)
(*                   how A should be decomposed.                             *)
(*   [u|d]submx A == the up/down submatrices of a column block matrix A.     *)
(* [u|d][l|r]submx A == the upper left, etc submatrices of a block matrix A. *)
(* castmx eq_mn A == A : 'M_(m, n) casted to 'M_(m', n') using the equation  *)
(*                   pair eq_mn : (m = m') * (n = n'). This is the usual     *)
(*                   workaround for the syntactic limitations of dependent   *)
(*                   types in Coq, and can be used to introduce a block      *)
(*                   decomposition. It simplifies to A when eq_mn is the     *)
(*                   pair (erefl m, erefl n) (using rewrite /castmx /=).     *)
(* conform_mx B A == A if A and B have the same dimensions, else B.          *)
(* In 'M[R]_(m, n), R can be any type, but 'M[R]_(m, n) inherits the eqType, *)
(* choiceType, countType, finType, and zmodType structures of R; however,    *)
(* because the type of matrices specifies their dimension, only non-trivial  *)
(* square matrices (of type 'M[R]_n.+1) can inherit the ring structure of R; *)
(* they can also inherit the unit ring structure of R when R is commutative. *)
(*   We thus provide separate syntax for the general matrix multiplication,  *)
(* and other operations for matrices over a ringType R:                      *)
(*         A *m B == the matrix product of A and B; the width of A must be   *)
(*                   equal to the height of B.                               *)
(*        a *m: A == the matrix A scaled by factor a. This will be subsumed  *)
(*                   by the *: operation of the vector space structure, but  *)
(*                   we need to define matrices first.                       *)
(*           a%:M == the scalar matrix with a's on the main diagonal; in     *)
(*                   particular 1%:M denotes the identity matrix, and is is  *)
(*                   equal to 1%R when n is of the form n'.+1 (e.g., n = 1). *)
(*      diag_mx d == the diagonal matrix whose main diagonal is d : 'rV_n.   *)
(*   delta_mx i j == the matrix with a 1 in row i, column j and 0 elsewhere. *)
(*       pid_mx r == the partial identity matrix with 1s only on the r first *)
(*                   coefficients of the main diagonal; the dimensions of    *)
(*                   pid_mx r are determined by the context, and can be      *)
(*                   rectangular.                                            *)
(*     copid_mx r == the complement to 1 of pid_mx r: a square matrix with   *)
(*                   1s on all but the first r coefficients on its main      *)
(*                   diagonal.                                               *)
(*      perm_mx s == the n x n permutation matrix for s : 'S_n.              *)
(* tperm_mx i1 i2 == the permutation matrix that exchanges i1 i2 : 'I_n.     *)
(*   is_perm_mx A == A is a permutation matrix.                              *)
(*     lift0_mx A == the 1 + n square matrix block_mx 1 0 0 A when A : 'M_n. *)
(*          \tr A == the trace of a square matrix A.                         *)
(*         \det A == the determinant of A, using the Leibnitz formula.       *)
(* cofactor i j A == the i, j cofactor of A (the signed i, j minor of A),    *)
(*         \adj A == the adjugate matrix of A (\adj A i j = cofactor j i A). *)
(*   A \in unitmx == A is invertible (R must be a comUnitRingType).          *)
(*        invmx A == the inverse matrix of A if A \in unitmx A, otherwise A. *)
(* The definition of the triangular decomposition, rank and row space        *)
(* operations are limited to matrices over a fieldType F:                    *)
(*    cormenLUP A == the triangular decomposition (L, U, P) of a nontrivial  *)
(*                   square matrix A into a lower triagular matrix L with 1s *)
(*                   on the main diagonal, an upper matrix U, and a          *)
(*                   permutation matrix P, such that P * A = L * U.          *)
(*      erankmx A == the extended rank decomposition (L, U, r) of A, with L  *)
(*                   a column permutation of a lower triangular invertible   *)
(*                   matrix, U a row permutation of an upper triangular      *)
(*                   invertible matrix, and r the rank of A, all satisfying  *)
(*                   the identity L *m pid_mx r *m U = A.                    *)
(*        \rank A == the rank of A.                                          *)
(*    row_free A <=> the rows of A are linearly free (i.e., the rank and     *)
(*                   height of A are equal).                                 *)
(*    row_full A <=> the row-space of A spans all row-vectors (i.e., the     *)
(*                   rank and width of A are equal).                         *)
(*    col_ebase A == the extended column basis of A (the first matrix L      *)
(*                   returned by emxrank A).                                 *)
(*    row_ebase A == the extended row base of A (the second matrix U         *)
(*                   returned by emxrank A).                                 *)
(*     col_base A == a basis for the columns of A: a row-full matrix         *)
(*                   consisting of the first \rank A columns of col_ebase A. *)
(*     row_base A == a basis for the rows of A: a row-free matrix consisting *)
(*                   of the first \rank A rows of row_ebase A.               *)
(*       pinvmx A == a partial inverse for A in its row space (or on its     *)
(*                   column space, equivalently). In particular, if u is a   *)
(*                   row vector in the row_space of A, then u *m pinvmx A is *)
(*                   the row vector of the coefficients of a decomposition   *)
(*                   of u as a sub of rows of A                              *)
(*        kermx A == the row kernel of A : a square matrix whose row space   *)
(*                   consists of all u such that u *m A = 0 (it consists of  *)
(*                   the inverse of col_ebase A, with the top \rank A rows   *)
(*                   zeroed out). Also, kermx A is a partial right inverse   *)
(*                   to col_ebase A, in the row space anihilated by A.       *)
(*      cokermx A == the cokernel of A : a square matrix whose column space  *)
(*                   consists of all v such that A *m v = 0 (it consists of  *)
(*                   the inverse of row_ebase A, with the leftmost \rank A   *)
(*                   columns zeroed out).                                    *)
(* We use a different scope %MS for matrix row-space set-like operations; to *)
(* avoid confusion, this scope should not be opened globally. Note that the  *)
(* the arguments of \rank _ and the operations below have default scope %MS. *)
(*    (A <= B)%MS <=> the row-space of A is included in the row-space of B.  *)
(*                   We test for this by testing if cokermx B anihilates A.  *)
(*  (A <= B <= C)%MS == (A <= B)%MS && (B && C)%MS                           *)
(*    (A == B)%MS == (A <= B <= A)%MS (A and B have the same row-space).     *)
(*   (A :=: B)%MS == A and B behave identically wrt. \rank and <=. This      *)
(*                   triple rewrite rule is the Prop version of (A == B)%MS. *)
(*                   Note that :=: cannot be treated as a setoid-style       *)
(*                   Equivalence because its arguments can have different    *)
(*                   types: A and B need not have the same number of rows,   *)
(*                   and often don't (e.g., in row_base A :=: A).            *)
(*       <<A>>%MS == a square matrix with the same row-space as A; <<A>>%MS  *)
(*                   is a canonical representation of the subspace generated *)
(*                   by A, viewed as a list of row-vectors: if (A == B)%MS,  *)
(*                   then <<A>>%MS = <<B>>%MS.                               *)
(*     (A + B)%MS == a square matrix whose row-space is the sum of the       *)
(*                   row-spaces of A and B; thus (A + B == col_mx A B)%MS.   *)
(*  (\sum_i <expr i>)%MS == the "big" version of (_ + _)%MS; as the latter   *)
(*                   has a canonical abelian monoid structure, most generic  *)
(*                   bigops lemmas apply (the other bigop indexing notations *)
(*                   are also defined).                                      *)
(*   (A :&: B)%MS == a square matrix whose row-space is the intersection of  *)
(*                   the row-spaces of A and B.                              *)
(*  (\bigcap_i <expr i>)%MS == the "big" version of (_ :&: _)%MS, which also *)
(*                   has a canonical abelian monoid structure.               *)
(*         A^C%MS == a square matrix whose row-space is a complement to the  *)
(*                   the row-space of A (it consists of row_ebase A with the *)
(*                   top \rank A rows zeroed out).                           *)
(*   (A :\: B)%MS == a square matrix whose row-space is a complement of the  *)
(*                   the row-space of (A :&: B)%MS in the row-space of A.    *)
(*                   We have (A :\: B == A :&: (capmx_gen A B)^C)%MS, with   *)
(*                   capmx_gen A B a recatangular matrix that generates      *)
(*                   (A :&: B)%MS, i.e., (capmx_gen A B == A :&: B)%MS.      *)
(*     mxdirect S == the sum expression S is a direct sum. This is a NON     *)
(*                   EXTENSIONAL notation: the exact boolean expression is   *)
(*                   inferred from the syntactic form of S (expanding        *)
(*                   definitions, however); both (\sum_(i | _) _)%MS and     *)
(*                   (_ + _)%MS sums are recognized. This construct uses a   *)
(*                   variant of the reflexive ("quote") canonical structure, *)
(*                   mxsum_expr. The structure also recognizes sums of       *)
(*                   matrix ranks, so that lemmas concerning the rank of     *)
(*                   direct sums can be used bidirectionally.                *)
(* Note that in this row-space theory, matrices represent vectors, subspaces *)
(* and also linear transformations.                                          *)
(*   We also extend any finType structure of R to 'M[R]_(m, n), and define   *)
(*     {'GL_n[R]} == the finGroupType of units of 'M[R]_n.-1.+1              *)
(*      'GL_n[R]  == the general linear group of all matrices in {'GL_n(R)}. *)
(*      'GL_n(p)  == 'GL_n['F_p], the general linear group of a prime field. *)
(*       GLval u  == the coercion of u : {'GL_n(R)} to a matrix.             *)
(*   In addition to the lemmas relevant to these definitions, this file also *)
(* proves several classic results, including :                               *)
(* - The determinant is a multilinear alternate form.                        *)
(* - The Laplace determinant expansion formulas: expand_det_[row|col].       *)
(* - The Cramer rule : mul_mx_adj & mul_adj_mx                               *)
(* - The Sylvester|Frobenius rank inequalities : mxrank_[mul_min|Frobenius]. *)
(* - The order of 'GL_n[F].                                                  *)
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

Reserved Notation "\matrix_ i E" 
  (at level 36, E at level 36, i at level 2,
   format "\matrix_ i  E").
Reserved Notation "\matrix_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\matrix_ ( i  <  n ) E").
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
Reserved Notation "A :+: B" (at level 50, left associativity).
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "A ^C"    (at level 8, format "A ^C").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").
Reserved Notation "\rank A" (at level 10, A at level 8, format "\rank  A").

Delimit Scope matrix_set_scope with MS.

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

Inductive matrix : predArgType := Matrix of {ffun 'I_m * 'I_n -> R}.

Definition mx_val A := let: Matrix g := A in g.

Canonical Structure matrix_subType :=
  Eval hnf in [newType for mx_val by matrix_rect].

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

Notation "\matrix_ i E" :=
  (matrix_of_fun (fun i j => fun_of_matrix E (@GRing.zero (Zp_zmodType 0)) j))
  : ring_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i < m ) E" :=
  (\matrix_(i < m, j < _) E 0 j) (only parsing) : ring_scope.

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
  Eval hnf in [eqMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_eqType (R : eqType) m n:=
  Eval hnf in EqType 'M[R]_(m, n) (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  [choiceMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_choiceType (R : choiceType) m n :=
  Eval hnf in ChoiceType 'M[R]_(m, n) (matrix_choiceMixin R m n).
Definition matrix_countMixin (R : countType) m n :=
  [countMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_countType (R : countType) m n :=
  Eval hnf in CountType 'M[R]_(m, n) (matrix_countMixin R m n).
Canonical Structure matrix_subCountType (R : countType) m n :=
  Eval hnf in [subCountType of 'M[R]_(m, n)].
Definition matrix_finMixin (R : finType) m n :=
  [finMixin of 'M[R]_(m, n) by <:].
Canonical Structure matrix_finType (R : finType) m n :=
  Eval hnf in FinType 'M[R]_(m, n) (matrix_finMixin R m n).
Canonical Structure matrix_subFinType (R : finType) m n :=
  Eval hnf in [subFinType of 'M[R]_(m, n)].

Lemma card_matrix : forall (F : finType) m n,
  (#|{: 'M[F]_(m, n)}| = #|F| ^ (m * n))%N.
Proof. by move=> F m n; rewrite card_sub card_ffun card_prod !card_ord. Qed.

(*****************************************************************************)
(****** Matrix structural operations (transpose, permutation, blocks) ********)
(*****************************************************************************)

Section MatrixStructural.

Variable R : Type.

(* Constant matrix *)
Definition const_mx m n a : 'M[R]_(m, n) := \matrix_(i, j) a.
Implicit Arguments const_mx [[m] [n]].

Section FixedDim.
(* Definitions and properties for which we can work with fixed dimensions. *)

Variables m n : nat.
Implicit Type A : 'M[R]_(m, n).

(* Reshape a matrix, to accomodate the block functions for instance. *)
Definition castmx m' n' (eq_mn : (m = m') * (n = n')) A : 'M_(m', n') :=
  let: erefl in _ = m' := eq_mn.1 return 'M_(m', n') in
  let: erefl in _ = n' := eq_mn.2 return 'M_(m, n') in A.

Definition conform_mx m' n' B A :=
  match m =P m', n =P n' with
  | ReflectT eq_m, ReflectT eq_n => castmx (eq_m, eq_n) A
  | _, _ => B
  end.

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

Lemma castmx_const : forall m' n' (eq_mn : (m = m') * (n = n')) a,
  castmx eq_mn (const_mx a) = const_mx a.
Proof. by rewrite /castmx => m' n' []; case: m /; case: n /. Qed.

Lemma trmx_const : forall a, trmx (const_mx a) = const_mx a.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma row_perm_const : forall s a, row_perm s (const_mx a) = const_mx a.
Proof. by move=> s a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_perm_const : forall s a, col_perm s (const_mx a) = const_mx a.
Proof. by move=> s a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma xrow_const : forall i1 i2 a, xrow i1 i2 (const_mx a) = const_mx a.
Proof. by move=> i1 i2; exact: row_perm_const. Qed.

Lemma xcol_const : forall j1 j2 a, xcol j1 j2 (const_mx a) = const_mx a.
Proof. by move=> j1 j2; exact: col_perm_const. Qed.

Lemma rowP : forall u v : 'rV[R]_n, u = v <-> u 0 =1 v 0.
Proof.
by move=> u v; split=> [-> // | eq_uv]; apply/matrixP=> i; rewrite [i]ord1.
Qed.

Lemma rowK : forall u_ i0, row i0 (\matrix_i u_ i) = u_ i0.
Proof. by move=> u_ i0; apply/rowP=> i'; rewrite !mxE. Qed.

Lemma row_matrixP : forall A B, (forall i, row i A = row i B) <-> A = B.
Proof.
move=> A B; split=> [eqAB | -> //]; apply/matrixP=> i j.
by move/rowP: (eqAB i); move/(_ j); rewrite !mxE.
Qed.

Lemma colP : forall u v : 'cV[R]_m, u = v <-> u^~ 0 =1 v^~ 0.
Proof.
by move=> u v; split=> [-> // | eq_uv]; apply/matrixP=> i j; rewrite [j]ord1.
Qed.

Lemma row_const : forall i0 a, row i0 (const_mx a) = const_mx a.
Proof. by move=> i0 a; apply/rowP=> j; rewrite !mxE. Qed.

Lemma col_const : forall j0 a, col j0 (const_mx a) = const_mx a.
Proof. by move=> j0 a; apply/colP=> i; rewrite !mxE. Qed.

Lemma row'_const : forall i0 a, row' i0 (const_mx a) = const_mx a.
Proof. by move=> i0 a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col'_const : forall j0 a, col' j0 (const_mx a) = const_mx a.
Proof. by move=> j0 a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma col_perm1 : forall A, col_perm 1 A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma row_perm1 : forall A, row_perm 1 A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE perm1. Qed.

Lemma col_permM : forall s t A, col_perm (s * t) A = col_perm s (col_perm t A).
Proof. by move=> s t A; apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma row_permM : forall s t A, row_perm (s * t) A = row_perm s (row_perm t A).
Proof. by move=> s t A; apply/matrixP=> i j; rewrite !mxE permM. Qed.

Lemma col_row_permC : forall s t A,
  col_perm s (row_perm t A) = row_perm t (col_perm s A).
Proof. by move=> s t A; apply/matrixP=> i j; rewrite !mxE. Qed.

End FixedDim.

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

(* This can be use to reverse an equation that involves a cast. *)
Lemma castmx_sym : forall m1 n1 m2 n2 (eq_m : m1 = m2) (eq_n : n1 = n2) A1 A2,
  A1 = castmx (eq_m, eq_n) A2 -> A2 = castmx (esym eq_m, esym eq_n) A1.
Proof. by symmetry; apply: (canLR (castmxK _ _)). Qed.

Lemma castmxE : forall m1 n1 m2 n2 (eq_mn : (m1 = m2) * (n1 = n2)) A i j,
  castmx eq_mn A i j =
     A (cast_ord (esym eq_mn.1) i) (cast_ord (esym eq_mn.2) j).
Proof.
by move=> m1 n1 m2 n2 []; case: m2 /; case: n2 / => A i j; rewrite !cast_ord_id.
Qed.

Lemma conform_mx_id : forall m n (B A : 'M_(m, n)), conform_mx B A = A.
Proof.
by rewrite /conform_mx => m n B A; do 2!case: eqP => // *; rewrite castmx_id.
Qed.

Lemma nonconform_mx : forall m m' n n' (B : 'M_(m', n')) (A : 'M_(m, n)),
  (m != m') || (n != n') -> conform_mx B A = B.
Proof. by rewrite /conform_mx => m m' n n' B A; do 2!case: eqP. Qed.

Lemma conform_castmx : forall m1 n1 m2 n2 m3 n3 (e : (m2 = m3) * (n2 = n3)),
  forall (B : 'M_(m1, n1)) A, conform_mx B (castmx e A) = conform_mx B A.
Proof. by move=> m1 n1 m2 n2 m3 n3 []; case: m3 /; case: n3 /. Qed.

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

Lemma row_id : forall n i (V : 'rV_n), row i V = V.
Proof. by move=> n i V; apply/rowP=> j; rewrite mxE [i]ord1. Qed.

Lemma col_id : forall n j (V : 'cV_n), col j V = V.
Proof. by move=> n j V; apply/colP=> i; rewrite mxE [j]ord1. Qed.

Lemma row_eq : forall m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  row i1 A1 = row i2 A2 -> A1 i1 =1 A2 i2.
Proof.
by move=> m1 m2 n i1 i2 A1 A2 eq12 j; move/rowP: eq12; move/(_ j); rewrite !mxE.
Qed.

Lemma col_eq : forall m n1 n2 j1 j2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  col j1 A1 = col j2 A2 -> A1^~ j1 =1 A2^~ j2.
Proof.
by move=> m n1 n2 j1 j2 A1 A2 eq12 i; move/colP: eq12; move/(_ i); rewrite !mxE.
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

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

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

Lemma row_mx_const : forall a, row_mx (const_mx a) (const_mx a) = const_mx a.
Proof. by move=> a; split_mxE. Qed.

Lemma col_mx_const : forall a, col_mx (const_mx a) (const_mx a) = const_mx a.
Proof. by move=> a; split_mxE. Qed.

End CutPaste.

Lemma trmx_lsub : forall m n1 n2 (A : 'M_(m, n1 + n2)),
  (lsubmx A)^T = usubmx A^T.
Proof. by move=> m n1 n2 A; split_mxE. Qed.

Lemma trmx_rsub : forall m n1 n2 (A : 'M_(m, n1 + n2)),
  (rsubmx A)^T = dsubmx A^T.
Proof. by move=> m n1 n2 A; split_mxE. Qed.

Lemma tr_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  (row_mx A1 A2)^T = col_mx A1^T A2^T.
Proof. by move=> m n1 n2 A1 A2; split_mxE. Qed.

Lemma tr_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  (col_mx A1 A2)^T = row_mx A1^T A2^T.
Proof. by move=> m1 m2 n A1 A2; split_mxE. Qed.

Lemma trmx_usub : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  (usubmx A)^T = lsubmx A^T.
Proof. by move=> m1 m2 n A; split_mxE. Qed.

Lemma trmx_dsub : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  (dsubmx A)^T = rsubmx A^T.
Proof. by move=> m1 m2 n A; split_mxE. Qed.

Lemma vsubmxK : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  col_mx (usubmx A) (dsubmx A) = A.
Proof.
move=> m1 m2 n A; apply: trmx_inj.
by rewrite tr_col_mx trmx_usub trmx_dsub hsubmxK.
Qed.

Lemma cast_row_mx : forall m m' n1 n2 (eq_m : m = m') A1 A2,
  castmx (eq_m, erefl _) (row_mx A1 A2)
    = row_mx (castmx (eq_m, erefl n1) A1) (castmx (eq_m, erefl n2) A2).
Proof. by move=> m m' n1 n2; case: m' /. Qed.

Lemma cast_col_mx : forall m1 m2 n n' (eq_n : n = n') A1 A2,
  castmx (erefl _, eq_n) (col_mx A1 A2)
    = col_mx (castmx (erefl m1, eq_n) A1) (castmx (erefl m2, eq_n) A2).
Proof. by move=> m1 m2 n n'; case: n' /. Qed.

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma row_mxA : forall m n1 n2 n3,
  forall (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (A3 : 'M_(m, n3)),
  let cast := (erefl m, esym (addnA n1 n2 n3)) in
  row_mx A1 (row_mx A2 A3) = castmx cast (row_mx (row_mx A1 A2) A3).
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
Definition row_mxAx := row_mxA. (* bypass Prenex Implicits. *)

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma col_mxA : forall m1 m2 m3 n,
  forall (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (A3 : 'M_(m3, n)),
  let cast := (esym (addnA m1 m2 m3), erefl n) in
  col_mx A1 (col_mx A2 A3) = castmx cast (col_mx (col_mx A1 A2) A3).
Proof. by move=> *; apply: trmx_inj; rewrite trmx_cast !tr_col_mx -row_mxA. Qed.
Definition col_mxAx := col_mxA. (* bypass Prenex Implicits. *)

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

Lemma block_mx_const : forall a,
  block_mx (const_mx a) (const_mx a) (const_mx a) (const_mx a) = const_mx a.
Proof. by move=> a; split_mxE. Qed.

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

(* This lemma has Prenex Implicits to help RL rewrititng with castmx_sym. *)
Lemma block_mxA : forall m1 m2 m3 n1 n2 n3,
  forall (A11 : 'M_(m1, n1)) (A12 : 'M_(m1, n2)) (A13 : 'M_(m1, n3)),
  forall (A21 : 'M_(m2, n1)) (A22 : 'M_(m2, n2)) (A23 : 'M_(m2, n3)),
  forall (A31 : 'M_(m3, n1)) (A32 : 'M_(m3, n2)) (A33 : 'M_(m3, n3)),
  let cast := (esym (addnA m1 m2 m3), esym (addnA n1 n2 n3)) in
  let row1 := row_mx A12 A13 in let col1 := col_mx A21 A31 in
  let row3 := row_mx A31 A32 in let col3 := col_mx A13 A23 in
  block_mx A11 row1 col1 (block_mx A22 A23 A32 A33)
    = castmx cast (block_mx (block_mx A11 A12 A21 A22) col3 row3 A33).
Proof.
move=> m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33 /=.
rewrite block_mxEh !col_mxA -cast_row_mx -block_mxEv -block_mxEh.
rewrite block_mxEv block_mxEh !row_mxA -cast_col_mx -block_mxEh -block_mxEv.
by rewrite castmx_comp etrans_id.
Qed.
Definition block_mxAx := block_mxA. (* Bypass Prenex Implicits *)

End MatrixStructural.

Implicit Arguments const_mx [R m n].
Implicit Arguments row_mxA [R m n1 n2 n3 A1 A2 A3].
Implicit Arguments col_mxA [R m1 m2 m3 n A1 A2 A3].
Implicit Arguments block_mxA
  [R m1 m2 m3 n1 n2 n3 A11 A12 A13 A21 A22 A23 A31 A32 A33].
Prenex Implicits const_mx castmx trmx lsubmx rsubmx usubmx dsubmx row_mx col_mx.
Prenex Implicits block_mx ulsubmx ursubmx dlsubmx drsubmx.
Prenex Implicits row_mxA col_mxA block_mxA.
Notation "A ^T" := (trmx A) : ring_scope.

(* Matrix parametricity. *)
Section MapMatrix.

Variables (aT rT : Type) (f : aT -> rT).

Definition map_mx m n (A : 'M_(m, n)) := \matrix_(i, j) f (A i j).

Notation "A ^f" := (map_mx A) : ring_scope.

Section OneMatrix.

Variables (m n : nat) (A : 'M[aT]_(m, n)).

Lemma map_trmx : A^f^T = A^T^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_const_mx : forall a, (const_mx a)^f = const_mx (f a) :> 'M_(m, n).
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_row : forall i, (row i A)^f = row i A^f.
Proof. by move=> i; apply/rowP=> j; rewrite !mxE. Qed.

Lemma map_col : forall j, (col j A)^f = col j A^f.
Proof. by move=> j; apply/colP=> i; rewrite !mxE. Qed.

Lemma map_row' : forall i0, (row' i0 A)^f = row' i0 A^f.
Proof. by move=> i0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_col' : forall j0, (col' j0 A)^f = col' j0 A^f.
Proof. by move=> j0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_row_perm : forall s, (row_perm s A)^f = row_perm s A^f.
Proof. by move=> s; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_col_perm : forall s, (col_perm s A)^f = col_perm s A^f.
Proof. by move=> s; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_xrow : forall i1 i2, (xrow i1 i2 A)^f = xrow i1 i2 A^f.
Proof. by move=> i1 i2; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_xcol : forall j1 j2, (xcol j1 j2 A)^f = xcol j1 j2 A^f.
Proof. by move=> j1 j2; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_castmx : forall m' n' c, (castmx c A)^f = castmx c A^f :> 'M_(m', n').
Proof. by move=> m' n' c; apply/matrixP=> i j; rewrite !(castmxE, mxE). Qed.

Lemma map_conform_mx : forall m' n' (B : 'M_(m', n')),
  (conform_mx B A)^f = conform_mx B^f A^f.
Proof.
move=> m' n'; case: (eqVneq (m, n) (m', n')) => [[<- <-] B|].
  by rewrite !conform_mx_id.
by rewrite negb_and => neq_mn B; rewrite !nonconform_mx.
Qed.

End OneMatrix.

Section Block.

Variables m1 m2 n1 n2 : nat.
Variables (Aul : 'M[aT]_(m1, n1)) (Aur : 'M[aT]_(m1, n2)).
Variables (Adl : 'M[aT]_(m2, n1)) (Adr : 'M[aT]_(m2, n2)).
Variables (Bh : 'M[aT]_(m1, n1 + n2)) (Bv : 'M[aT]_(m1 + m2, n1)).
Variable B : 'M[aT]_(m1 + m2, n1 + n2).

Lemma map_row_mx : (row_mx Aul Aur)^f = row_mx Aul^f Aur^f.
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_col_mx : (col_mx Aul Adl)^f = col_mx Aul^f Adl^f.
Proof. by apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_block_mx :
  (block_mx Aul Aur Adl Adr)^f = block_mx Aul^f Aur^f Adl^f Adr^f.
Proof. by apply/matrixP=> i j; do 3![rewrite !mxE //; case: split => ?]. Qed.

Lemma map_lsubmx : (lsubmx Bh)^f = lsubmx Bh^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_rsubmx : (rsubmx Bh)^f = rsubmx Bh^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_usubmx : (usubmx Bv)^f = usubmx Bv^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_dsubmx : (dsubmx Bv)^f = dsubmx Bv^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_ulsubmx : (ulsubmx B)^f = ulsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_ursubmx : (ursubmx B)^f = ursubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_dlsubmx : (dlsubmx B)^f = dlsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_drsubmx : (drsubmx B)^f = drsubmx B^f.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End Block.

End MapMatrix.

(*****************************************************************************)
(********************* Matrix Zmodule (additive) structure *******************)
(*****************************************************************************)

Section MatrixZmodule.

Variable M : zmodType.

Section FixedDim.

Variables m n : nat.
Implicit Types A B : 'M[M]_(m, n).

Definition oppmx A := \matrix_(i, j) (- A i j).
Definition addmx A B := \matrix_(i, j) (A i j + B i j).
(* In principle, diag_mx and scalar_mx could be defined here, but since they *)
(* only make sense with the graded ring operations, we defer them to the     *)
(* next section.                                                             *)

Lemma addmxA : associative addmx.
Proof. by move=> A B C; apply/matrixP=> i j; rewrite !mxE addrA. Qed.

Lemma addmxC : commutative addmx.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE addrC. Qed.

Lemma add0mx : left_id (const_mx 0) addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE add0r. Qed.

Lemma addNmx : left_inverse (const_mx 0) oppmx addmx.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE addNr. Qed.

Definition matrix_zmodMixin := ZmodMixin addmxA addmxC add0mx addNmx.
Canonical Structure matrix_zmodType :=
  Eval hnf in ZmodType 'M[M]_(m, n) matrix_zmodMixin.

Lemma const_mx0 : const_mx 0 = 0. Proof. by []. Qed.
Lemma const_mxN : forall a, const_mx (- a) = - const_mx a.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE. Qed.
Lemma const_mx_add : forall a b, const_mx (a + b) = const_mx a + const_mx b.
Proof. by move=> a b; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mulmxnE : forall A d i j, (A *+ d) i j = A i j *+ d.
Proof. by move=> A d i j; elim: d => [|d IHd]; rewrite ?mulrS mxE ?IHd. Qed.

Lemma summxE : forall I r (P : pred I) (E : I -> 'M_(m, n)) i j,
  (\sum_(k <- r | P k) E k) i j = \sum_(k <- r | P k) E k i j.
Proof.
move=> I r P E i j.
by apply: (big_morph (fun A => A i j)) => [A B|]; rewrite mxE.
Qed.

End FixedDim.

Lemma flatmx0 : forall n, all_equal_to (0 : 'M_(0, n)).
Proof. by move=> n A; apply/matrixP=> [] []. Qed.

Lemma thinmx0 : forall n, all_equal_to (0 : 'M_(n, 0)).
Proof. by move=> n A; apply/matrixP=> i []. Qed.

Lemma trmx0 : forall m n, (0 : 'M_(m, n))^T = 0.
Proof. by move=> m n; exact: trmx_const. Qed.

Lemma trmx_add : forall m n (A B : 'M_(m, n)), (A + B)^T = A^T + B^T .
Proof. by move=> m n A B; apply/matrixP=> i j; rewrite !mxE. Qed.

(* Interaction of permx/xrow/xcol with the Zmodule operations should be *)
(* handled via the decomposition to product with a permutation matrix.  *)

Lemma row0 : forall m n i0, row i0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n i0; exact: row_const. Qed.

Lemma col0 : forall m n j0, col j0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n j0; exact: col_const. Qed.

Lemma row'0 : forall m n i0, row' i0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n i0; exact: row'_const. Qed.

Lemma col'0 : forall m n j0, col' j0 (0 : 'M_(m, n)) = 0.
Proof. by move=> m n j0; exact: col'_const. Qed.

Lemma row_mx0 : forall m n1 n2, row_mx 0 0 = 0 :> 'M_(m, n1 + n2).
Proof. by move=> m n1 n2; exact: row_mx_const. Qed.

Lemma col_mx0 : forall m1 m2 n, col_mx 0 0 = 0 :> 'M_(m1 + m2, n).
Proof. by move=> m1 m2 n; exact: col_mx_const. Qed.

Lemma block_mx0 : forall m1 m2 n1 n2,
  block_mx 0 0 0 0 = 0 :> 'M_(m1 + m2, n1 + n2).
Proof. by move=> m1 m2 n1 n2; exact: block_mx_const. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma opp_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  - row_mx A1 A2 = row_mx (- A1) (- A2).
Proof. by move=> *; split_mxE. Qed.

Lemma opp_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  - col_mx A1 A2 = col_mx (- A1) (- A2).
Proof. by move=> *; split_mxE. Qed.

Lemma opp_block_mx : forall m1 m2 n1 n2,
  forall (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)),
  - block_mx Aul Aur Adl Adr = block_mx (- Aul) (- Aur) (- Adl) (- Adr).
Proof. by move=> *; rewrite opp_col_mx !opp_row_mx. Qed.

Lemma add_row_mx : forall m n1 n2 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) B1 B2,
  row_mx A1 A2 + row_mx B1 B2 = row_mx (A1 + B1) (A2 + B2).
Proof. by move=> *; split_mxE. Qed.

Lemma add_col_mx : forall m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) B1 B2,
  col_mx A1 A2 + col_mx B1 B2 = col_mx (A1 + B1) (A2 + B2).
Proof. by move=> *; split_mxE. Qed.

Lemma add_block_mx : forall m1 m2 n1 n2,
  forall (Aul : 'M_(m1, n1)) Aur Adl (Adr : 'M_(m2, n2)) Bul Bur Bdl Bdr,
  let A := block_mx Aul Aur Adl Adr  in let B := block_mx Bul Bur Bdl Bdr in
  A + B = block_mx (Aul + Bul) (Aur + Bur) (Adl + Bdl) (Adr + Bdr).
Proof. by move=> *; rewrite add_col_mx !add_row_mx. Qed.

End MatrixZmodule.

Section FinZmodMatrix.
Variables (M : finZmodType) (m n : nat).
Local Notation MM := 'M[M]_(m, n).
Canonical Structure matrix_finZmodType := Eval hnf in [finZmodType of MM].
Canonical Structure matrix_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of MM for +%R].
Canonical Structure matrix_finGroupType :=
  Eval hnf in [finGroupType of MM for +%R].
End FinZmodMatrix.

(*****************************************************************************)
(*********** Matrix ring module, graded ring, and ring structures ************)
(*****************************************************************************)

Section MatrixAlgebra.

Variable R : ringType.

Section RingModule.

(* The ring module/vector space structure *)

Variables m n : nat.
Implicit Types A B : 'M[R]_(m, n).

Definition scalemx x A := \matrix_(i < m, j < n) (x * A i j).

(* Basis *)
Definition delta_mx i0 j0 : 'M[R]_(m, n) :=
  \matrix_(i < m, j < n) ((i == i0) && (j == j0))%:R.

Local Notation "x *m: A" := (scalemx x A) : ring_scope.

Lemma scalemx_const : forall a b, a *m: const_mx b = const_mx (a * b).
Proof. by move=> a b; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma scale0mx : forall A, 0 *m: A = 0.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE mul0r. Qed.

Lemma scalemx0 : forall x, x *m: 0 = 0.
Proof. by move=> x; apply/matrixP=> i j; rewrite !mxE mulr0. Qed.

Lemma scale1mx : forall A, 1 *m: A = A.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE mul1r. Qed.

Lemma scaleNmx : forall x A, (- x) *m: A = - (x *m: A).
Proof. by move=> x A; apply/matrixP=> i j; rewrite !mxE mulNr. Qed.

Lemma scaleN1mx : forall A, (- 1) *m: A = - A.
Proof. by move=> A; rewrite scaleNmx scale1mx. Qed.

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

Lemma scalemx_nat : forall d A, d%:R *m: A = A *+ d.
Proof.
move=> d A; elim: d => [|d IHd]; rewrite ?scale0mx //.
by rewrite !mulrS scalemx_addl scale1mx IHd.
Qed.

Lemma scalemx_suml : forall A I r (P : pred I) a_,
   (\sum_(i <- r | P i) a_ i) *m: A = \sum_(i <- r | P i) a_ i *m: A.
Proof.
move=> A; apply: (big_morph (scalemx^~ A)) => [a b|]; last exact: scale0mx.
by rewrite scalemx_addl.
Qed.

Lemma scalemx_sumr : forall a I r (P : pred I) eA_,
   a *m: (\sum_(i <- r | P i) eA_ i) = \sum_(i <- r | P i) a *m: eA_ i.
Proof.
move=> a; apply: (big_morph (scalemx a)) => [A B|]; last exact: scalemx0.
by rewrite scalemx_addr.
Qed.

Lemma matrix_sum_delta : forall A,
  A = \sum_(i < m) \sum_(j < n) A i j *m: delta_mx i j.
Proof.
move=> A; apply/matrixP=> i j.
rewrite summxE (bigD1 i) // summxE (bigD1 j) //= !mxE !eqxx mulr1.
rewrite !big1 ?addr0 //= => [i' | j']; rewrite eq_sym; move/negbTE=> diff.
  by rewrite summxE big1 // => j' _; rewrite !mxE diff mulr0.
by rewrite !mxE eqxx diff mulr0.
Qed.

End RingModule.

Notation "x *m: A" := (scalemx x A) : ring_scope.

Lemma trmx_delta : forall m n i j,
  (delta_mx i j)^T = delta_mx j i :> 'M[R]_(n, m).
Proof. by move=> m n i j; apply/matrixP=> i' j'; rewrite !mxE andbC. Qed.

Lemma trmx_scale : forall m n a (A  : 'M_(m, n)), (a *m: A)^T = a *m: A^T.
Proof. by move=> m n a A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma row_sum_delta : forall n (u : 'rV_n),
  u = \sum_(j < n) u 0 j *m: delta_mx 0 j.
Proof. by move=> n u; rewrite {1}[u]matrix_sum_delta big_ord1. Qed.

Ltac split_mxE := apply/matrixP=> i j; do ![rewrite mxE | case: split => ?].

Lemma scale_row_mx : forall m n1 n2 a (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  a *m: row_mx A1 A2 = row_mx (a *m: A1) (a *m: A2).
Proof. by move=> *; split_mxE. Qed.

Lemma scale_col_mx : forall m1 m2 n a (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  a *m: col_mx A1 A2 = col_mx (a *m: A1) (a *m: A2).
Proof. by move=> *; split_mxE. Qed.

Lemma scale_block_mx : forall m1 m2 n1 n2 a,
                       forall (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)),
                       forall (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2)),
  a *m: block_mx Aul Aur Adl Adr
     = block_mx (a *m: Aul) (a *m: Aur) (a *m: Adl) (a *m: Adr).
Proof. by move=> *; rewrite scale_col_mx !scale_row_mx. Qed.

(* Diagonal matrices *)

Lemma mulrb : forall (x : R) (b : bool), x *+ b = (if b then x else 0).
Proof. by move=> x []. Qed.

Definition diag_mx n (d : 'rV[R]_n) := \matrix_(i, j) (d 0 i *+ (i == j)).

Lemma tr_diag_mx : forall n (d : 'rV_n), (diag_mx d)^T = diag_mx d.
Proof.
by move=> n d; apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->.
Qed.

Lemma diag_mx0 : forall n, diag_mx 0 = 0 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxE mul0rn. Qed.

Lemma diag_mx_opp : forall n (d : 'rV_n), diag_mx (- d) = - diag_mx d.
Proof. by move=> n d; apply/matrixP=> i j; rewrite !mxE oppr_muln. Qed.

Lemma diag_mx_add : forall n (d e : 'rV_n),
  diag_mx (d + e) = diag_mx d + diag_mx e.
Proof. by move=> n d e; apply/matrixP=> i j; rewrite !mxE mulrn_addl. Qed.

Lemma scale_diag_mx : forall n a (d : 'rV_n),
  a *m: diag_mx d = diag_mx (a *m: d).
Proof. by move=> n a d; apply/matrixP=> i j; rewrite !mxE mulrnAr. Qed.

Lemma diag_mx_sum_delta : forall n (d : 'rV_n),
  diag_mx d = \sum_i d 0 i *m: delta_mx i i.
Proof.
move=> n d; apply/matrixP=> i j; rewrite summxE (bigD1 i) //= !mxE eqxx /=.
rewrite eq_sym mulr_natr big1 ?addr0 // => i' ne_i'i.
by rewrite !mxE eq_sym (negbTE ne_i'i) mulr0.
Qed.

(* Scalar matrix : a diagonal matrix with a constant on the diagonal *)
Definition scalar_mx n x : 'M[R]_n := \matrix_(i , j) (x *+ (i == j)).
Notation "x %:M" := (scalar_mx _ x) : ring_scope.

Lemma diag_const_mx : forall n a, diag_mx (const_mx a) = a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mx11_scalar : forall A : 'M_1, A = (A 0 0)%:M.
Proof. by move=> A; apply/rowP=> j; rewrite [j]ord1 mxE. Qed.

Lemma tr_scalar_mx : forall n a, (a%:M)^T = a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE eq_sym. Qed.

Lemma trmx1 : forall n, (1%:M)^T = 1%:M :> 'M_n.
Proof. move=> n; exact: tr_scalar_mx. Qed.

Lemma scalar_mx0 : forall n, 0%:M = 0 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxE mul0rn. Qed.

Lemma scalar_mx_opp : forall n a, (- a)%:M = - a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE oppr_muln. Qed.

Lemma scalar_mx_add : forall n a b, (a + b)%:M = a%:M + b%:M :> 'M_n.
Proof. by move=> n a b; apply/matrixP=> i j; rewrite !mxE mulrn_addl. Qed.

Lemma scale_scalar_mx : forall n a1 a2, a1 *m: a2%:M = (a1 * a2)%:M :> 'M_n.
Proof. by move=> n a1 a2; apply/matrixP=> i j; rewrite !mxE mulrnAr. Qed.

Lemma scalemx1 : forall n a, a *m: 1%:M = a%:M :> 'M_n.
Proof. by move=> n a; rewrite scale_scalar_mx mulr1. Qed.

Lemma scalar_mx_block : forall n1 n2 a,
  a%:M = block_mx a%:M 0 0 a%:M :> 'M_(n1 + n2).
Proof.
move=> n1 n2 a; apply/matrixP=> i j; rewrite !mxE -val_eqE /=.
by do 2![case: splitP => ? ->; rewrite !mxE];
   rewrite ?eqn_addl // -?(eq_sym (n1 + _)%N) eqn_leq leqNgt lshift_subproof.
Qed.

Lemma scalar_mx_sum_delta : forall n a,
  a%:M = \sum_i a *m: delta_mx i i :> 'M_n.
Proof.
move=> n a; rewrite -diag_const_mx diag_mx_sum_delta.
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma mx1_sum_delta : forall n, 1%:M = \sum_i delta_mx i i :> 'M_n.
Proof.
by move=> n; rewrite [1%:M]scalar_mx_sum_delta -scalemx_sumr scale1mx.
Qed.

Lemma row1 : forall n (i : 'I_n), row i 1%:M = delta_mx 0 i.
Proof. by move=> n i; apply/rowP=> j; rewrite !mxE eq_sym. Qed.

(* Matrix multiplication with the bigops *)
Definition mulmx {m n p} (A : 'M_(m, n)) (B : 'M_(n, p)) : 'M[R]_(m, p) :=
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

Lemma mulmx_subl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 - A2) *m B = A1 *m B - A2 *m B.
Proof. by move=> m n p A1 A2 B; rewrite mulmx_addl mulNmx. Qed.

Lemma mulmx_subr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 - B2) = A *m B1 - A *m B2.
Proof. by move=> m n p A1 A2 B; rewrite mulmx_addr mulmxN. Qed.

Lemma mulmx_suml : forall m n p (A : 'M_(n, p)) I r P (B_ : I -> 'M_(m, n)),
   (\sum_(i <- r | P i) B_ i) *m A = \sum_(i <- r | P i) B_ i *m A.
Proof.
move=> m n p A; apply: (big_morph (mulmx^~ A)) => [B C|]; last exact: mul0mx.
by rewrite mulmx_addl.
Qed.

Lemma mulmx_sumr : forall m n p (A : 'M_(m, n)) I r P (B_ : I -> 'M_(n, p)),
   A *m (\sum_(i <- r | P i) B_ i) = \sum_(i <- r | P i) A *m B_ i.
Proof.
move=> m n p A; apply: (big_morph (mulmx A)) => [B C|]; last exact: mulmx0.
by rewrite mulmx_addr.
Qed.

Lemma scalemxAl : forall m n p a (A : 'M_(m, n)) (B : 'M_(n, p)),
  a *m: (A *m B) = (a *m: A) *m B.
Proof.
move=> m n p a A B; apply/matrixP=> i k; rewrite !mxE big_distrr /=.
by apply: eq_bigr => j _; rewrite mulrA mxE.
Qed.
(* Right scaling associativity requires a commutative ring *)

Lemma rowE : forall m n i (A : 'M_(m, n)), row i A = delta_mx 0 i *m A.
Proof.
move=> m n i A; apply/rowP=> j; rewrite !mxE (bigD1 i) //= mxE !eqxx mul1r.
by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mul0r.
Qed.

Lemma row_mul : forall m n p (i : 'I_m) A (B : 'M_(n, p)),
  row i (A *m B) = row i A *m B.
Proof. by move=> m n p i A B; rewrite !rowE mulmxA. Qed.

Lemma mulmx_sum_row : forall m n (u : 'rV_m) (A : 'M_(m, n)),
  u *m A = \sum_i u 0 i *m: row i A.
Proof.
move=> m n u A; apply/rowP=> j; rewrite mxE summxE; apply: eq_bigr => i _.
by rewrite !mxE.
Qed.

Lemma mul_delta_mx_cond : forall m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p),
  delta_mx i1 j1 *m delta_mx j2 k2 = delta_mx i1 k2 *+ (j1 == j2).
Proof.
move=> m n p j1 j2 i1 k2; apply/matrixP=> i k; rewrite !mxE (bigD1 j1) //=.
rewrite mulmxnE !mxE !eqxx andbT -natr_mul -mulrnA !mulnb !andbA andbAC.
by rewrite big1 ?addr0 // => j; rewrite !mxE andbC -natr_mul; move/negbTE->.
Qed.

Lemma mul_delta_mx : forall m n p (j : 'I_n) (i : 'I_m) (k : 'I_p),
  delta_mx i j *m delta_mx j k = delta_mx i k.
Proof. by move=> m n p j i k; rewrite mul_delta_mx_cond eqxx. Qed.

Lemma mul_delta_mx_0 : forall m n p (j1 j2 : 'I_n) (i1 : 'I_m) (k2 : 'I_p),
  j1 != j2 -> delta_mx i1 j1 *m delta_mx j2 k2 = 0.
Proof.
by move=> m n p j1 j2 i1 k2; rewrite mul_delta_mx_cond; move/negbTE->.
Qed.

Lemma mul_diag_mx : forall m n d (A : 'M_(m, n)),
  diag_mx d *m A = \matrix_(i, j) (d 0 i * A i j).
Proof.
move=> m n d A; apply/matrixP=> i j.
rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAl; move/negbTE->.
Qed.

Lemma mul_mx_diag : forall m n (A : 'M_(m, n)) d,
  A *m diag_mx d = \matrix_(i, j) (A i j * d 0 j).
Proof.
move=> m n A d; apply/matrixP=> i j.
rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
by rewrite mxE eq_sym mulrnAr; move/negbTE->.
Qed.

Lemma mulmx_diag : forall n (d e : 'rV_n),
  diag_mx d *m diag_mx e = diag_mx (\row_j (d 0 j * e 0 j)).
Proof.
by move=> n d e; apply/matrixP=> i j; rewrite mul_diag_mx !mxE mulrnAr.
Qed.

Lemma mul_scalar_mx : forall m n a (A : 'M_(m, n)), a%:M *m A = a *m: A.
Proof.
move=> m n a A; rewrite -diag_const_mx mul_diag_mx.
by apply/matrixP=> i j; rewrite !mxE.
Qed.

Lemma scalar_mxM : forall n a b, (a * b)%:M = a%:M *m b%:M :> 'M_n.
Proof. by move=> n a b; rewrite mul_scalar_mx scale_scalar_mx. Qed.

Lemma mul1mx : forall m n (A : 'M_(m, n)), 1%:M *m A = A.
Proof. by move=> m n A; rewrite mul_scalar_mx scale1mx. Qed.

Lemma mulmx1 : forall m n (A : 'M_(m, n)), A *m 1%:M = A.
Proof.
move=> m n A; rewrite -diag_const_mx mul_mx_diag.
by apply/matrixP=> i j; rewrite !mxE mulr1.
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
  \matrix_(i, j) ((i == j :> nat) && (i < r))%:R.

Lemma pid_mx_0 : forall m n, pid_mx 0 = 0 :> 'M_(m, n).
Proof. by move=> m n; apply/matrixP=> i j; rewrite !mxE andbF. Qed.

Lemma pid_mx_1 : forall r, pid_mx r = 1%:M :> 'M_r.
Proof. by move=> r; apply/matrixP=> i j; rewrite !mxE ltn_ord andbT. Qed.

Lemma pid_mx_row : forall n r, pid_mx r = row_mx 1%:M 0 :> 'M_(r, r + n).
Proof.
move=> n r; apply/matrixP=> i j; rewrite !mxE ltn_ord andbT.
case: splitP => j' ->; rewrite !mxE // .
by rewrite eqn_leq andbC leqNgt lshift_subproof.
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
by rewrite eqn_leq andbC leqNgt lshift_subproof.
Qed.

Lemma tr_pid_mx : forall m n r, (pid_mx r)^T = pid_mx r :> 'M_(n, m).
Proof.
by move=> m n r; apply/matrixP=> i j; rewrite !mxE eq_sym; case: eqP => // ->.
Qed.

Lemma pid_mx_minv : forall m n r, pid_mx (minn m r) = pid_mx r :> 'M_(m, n).
Proof. by move=> m n r; apply/matrixP=> i j; rewrite !mxE leq_minr ltn_ord. Qed.
 
Lemma pid_mx_minh : forall m n r, pid_mx (minn n r) = pid_mx r :> 'M_(m, n).
Proof. by move=> m n r; apply: trmx_inj; rewrite !tr_pid_mx pid_mx_minv. Qed.

Lemma mul_pid_mx : forall m n p q r,
  (pid_mx q : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx (minn n (minn q r)).
Proof.
move=> m n p q r; apply/matrixP=> i k; rewrite !mxE !leq_minr.
case: leqP => [le_n_i | lt_i_n].
  rewrite andbF big1 // => j _.
  by rewrite -pid_mx_minh !mxE leq_minr ltnNge le_n_i andbF mul0r.
rewrite (bigD1 (Ordinal lt_i_n)) //= big1 ?addr0 => [|j].
  by rewrite !mxE eqxx /= -natr_mul mulnb andbCA.
by rewrite -val_eqE /= !mxE eq_sym -natr_mul; move/negbTE=> ->.
Qed.

Lemma pid_mx_id : forall m n p r,
  r <= n -> (pid_mx r : 'M_(m, n)) *m (pid_mx r : 'M_(n, p)) = pid_mx r.
Proof. by move=> m n p r le_r_n; rewrite mul_pid_mx minnn minnr. Qed.

Definition copid_mx {n} r : 'M_n := 1%:M - pid_mx r.

Lemma mul_copid_mx_pid : forall m n r,
  r <= m -> copid_mx r *m pid_mx r = 0 :> 'M_(m, n).
Proof. by move=> m n r le_r_m; rewrite mulmx_subl mul1mx pid_mx_id ?subrr. Qed.

Lemma mul_pid_mx_copid : forall m n r,
  r <= n -> pid_mx r *m copid_mx r = 0 :> 'M_(m, n).
Proof. by move=> m n r le_r_n; rewrite mulmx_subr mulmx1 pid_mx_id ?subrr. Qed.

Lemma copid_mx_id : forall n r,
  r <= n -> copid_mx r *m copid_mx r = copid_mx r :> 'M_n.
Proof.
by move=> n r le_r_n; rewrite mulmx_subl mul1mx mul_pid_mx_copid // oppr0 addr0.
Qed.

(* Block products; we cover all 1 x 2, 2 x 1, and 2 x 2 block products. *)

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

Lemma mxtrace_diag : forall n (D : 'rV_n), \tr (diag_mx D) = \sum_j D 0 j.
Proof. by move=> n D; apply: eq_bigr => j _; rewrite mxE eqxx. Qed.

Lemma mxtrace_scalar : forall n a, \tr (a%:M : 'M_n) = a *+ n.
Proof.
move=> n a; rewrite -diag_const_mx mxtrace_diag.
by rewrite (eq_bigr _ (fun j _ => mxE _ 0 j)) sumr_const card_ord.
Qed.

Lemma mxtrace1 : forall n, \tr (1%:M : 'M_n) = n%:R.
Proof. by move=> n; exact: mxtrace_scalar. Qed.

Lemma trace_mx11 : forall A : 'M_1, \tr A = A 0 0.
Proof. by move=> A; rewrite {1}[A]mx11_scalar mxtrace_scalar. Qed.

Lemma mxtrace_block : forall n1 n2 (Aul : 'M_n1) Aur Adl (Adr : 'M_n2),
  \tr (block_mx Aul Aur Adl Adr) = \tr Aul + \tr Adr.
Proof.
move=> n1 n2 Aul Aur Adl Adr; rewrite /(\tr _) big_split_ord /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite (block_mxEul, block_mxEdr).
Qed.

(* Matrix ring Structure : now structural (dimension of the form n.+1) *)
Section MatrixRing.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma matrix_nonzero1 : 1%:M != 0 :> 'M_n.
Proof.
by apply/eqP; move/matrixP; move/(_ 0 0); move/eqP; rewrite !mxE oner_eq0.
Qed.

Definition matrix_ringMixin :=
  RingMixin (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
            (@mulmx_addl n n n) (@mulmx_addr n n n) matrix_nonzero1.
Canonical Structure matrix_ringType :=
  Eval hnf in RingType 'M[R]_n  matrix_ringMixin.

Lemma mulmxE : mulmx = *%R. Proof. by []. Qed.
Lemma idmxE : 1%:M = 1 :> 'M_n. Proof. by []. Qed.

Lemma scalar_mxRM : GRing.morphism (@scalar_mx n).
Proof.
by split=> // a b; rewrite ?scalar_mxM ?scalar_mx_add ?scalar_mx_opp.
Qed.

End MatrixRing.

Section LiftPerm.

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

End LiftPerm.

(* Determinants and adjugates are defined here, but most of their properties *)
(* only hold for matrices over a commutative ring, so their theory is        *)
(* deferred to that section.                                                 *)

(* The determinant, in one line with the Leibniz Formula *)
Definition determinant n (A : 'M_n) : R :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i).

(* The cofactor of a matrix on the indexes i and j *)
Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * determinant (row' i (col' j A)).

(* The adjugate matrix : defined as the transpose of the matrix of cofactors *)
Definition adjugate n (A : 'M_n) := \matrix_(i, j) cofactor A j i.

End MatrixAlgebra.

Implicit Arguments delta_mx [R m n].
Implicit Arguments scalar_mx [R n].
Implicit Arguments perm_mx [R n].
Implicit Arguments tperm_mx [R n].
Implicit Arguments pid_mx [R m n].
Implicit Arguments copid_mx [R n].
Prenex Implicits delta_mx diag_mx scalar_mx perm_mx tperm_mx pid_mx copid_mx.
Prenex Implicits scalemx mulmx mxtrace determinant cofactor adjugate.
Notation "a *m: A" := (scalemx a A) : ring_scope.
Notation "a %:M" := (scalar_mx a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "\tr A" := (mxtrace A) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.
Implicit Arguments mul_delta_mx [R m n p].
Implicit Arguments scalar_mxRM [R n'].
Prenex Implicits mul_delta_mx scalar_mxRM.

(* Non-commutative transpose requires multiplication in the converse ring.   *)
Lemma trmx_mul_rev : forall (R : ringType) m n p,
    let R' := RevRingType R in forall (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)),
  (A *m B)^T = (B : 'M[R']_(n, p))^T *m (A : 'M[R']_(m, n))^T.
Proof.
move=> R m n p /= A B; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite !mxE.
Qed.

Canonical Structure matrix_finRingType (R : finRingType) n' :=
  Eval hnf in [finRingType of 'M[R]_n'.+1].

(* Parametricity over the algebra structure; since ssralg does't have        *)
(* support for purely additive morphisms, we only work at the ring level.    *)
Section MapRingMatrix.

Variables (aR rR : ringType) (f : aR -> rR).
Hypothesis fRM : GRing.morphism f.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section FixedSize.

Variables m n p : nat.
Implicit Type A : 'M[aR]_(m, n).

Lemma map_mx0 : 0^f = 0 :> 'M_(m, n).
Proof. by rewrite map_const_mx ringM_0. Qed.

Lemma map_mxN : forall A,  (- A)^f = - A^f.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE ringM_opp. Qed.

Lemma map_mxD : forall A B, (A + B)^f = A^f + B^f.
Proof. by move=> A B; apply/matrixP=> i j; rewrite !mxE ringM_add. Qed.

Lemma map_mx_mulnat : forall A d, (A *+ d)^f = A^f *+ d.
Proof. by move=> A; elim=> [|d IHd]; rewrite ?map_mx0 ?mulrS ?map_mxD ?IHd. Qed.

Lemma map_mx_sub : forall A B, (A - B)^f =  A^f - B^f.
Proof. by move=> A B; rewrite map_mxD map_mxN. Qed.

Definition map_mx_sum := big_morph _ map_mxD map_mx0.

Lemma map_mxZ : forall a A, (a *m: A)^f = f a *m: A^f.
Proof. by move=> a A; apply/matrixP=> i j; rewrite !mxE ringM_mul. Qed.

Lemma map_mxM : forall A B, (A *m B)^f = A^f *m B^f :> 'M_(m, p).
Proof.
move=> A B; apply/matrixP=> i k; rewrite !mxE ringM_sum //.
by apply: eq_bigr => j; rewrite !mxE ringM_mul.
Qed.

Lemma map_delta_mx : forall i j, (delta_mx i j)^f = delta_mx i j :> 'M_(m, n).
Proof. by move=> i j; apply/matrixP=> i' j'; rewrite !mxE ringM_nat. Qed.

Lemma map_diag_mx : forall d, (diag_mx d)^f = diag_mx d^f :> 'M_n.
Proof. by move=> d; apply/matrixP=> i j; rewrite !mxE ringM_natmul. Qed.

Lemma map_scalar_mx : forall a, a%:M^f = (f a)%:M :> 'M_n.
Proof. by move=> a; apply/matrixP=> i j; rewrite !mxE ringM_natmul. Qed.

Lemma map_mx1 : 1%:M^f = 1%:M :> 'M_n.
Proof. by rewrite map_scalar_mx ringM_1. Qed.

Lemma map_perm_mx : forall s : 'S_n, (perm_mx s)^f = perm_mx s.
Proof. by move=> s; apply/matrixP=> i j; rewrite !mxE ringM_nat. Qed.

Lemma map_tperm_mx : forall i1 i2 : 'I_n, (tperm_mx i1 i2)^f = tperm_mx i1 i2.
Proof. by move=> i j; exact: map_perm_mx. Qed.

Lemma map_pid_mx : forall r, (pid_mx r)^f = pid_mx r :> 'M_(m, n).
Proof. by move=> r; apply/matrixP=> i j; rewrite !mxE ringM_nat. Qed.

Lemma trace_map_mx : forall A : 'M_n, \tr A^f = f (\tr A).
Proof.
by move=> A; rewrite ringM_sum //; apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma det_map_mx : forall n' (A : 'M_n'), \det A^f = f (\det A).
Proof.
move=> n' A; rewrite ringM_sum //; apply: eq_bigr => s _.
rewrite ringM_mul // ringM_sign // (ringM_prod fRM); congr (_ * _).
by apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma cofactor_map_mx : forall (A : 'M_n) i j,
  cofactor A^f i j = f (cofactor A i j).
Proof.
by move=> A i j; rewrite ringM_mul ?ringM_sign // -det_map_mx map_row' map_col'.
Qed.

Lemma map_mx_adj : forall A : 'M_n, (\adj A)^f = \adj A^f.
Proof. by move=> A; apply/matrixP=> i j; rewrite !mxE cofactor_map_mx. Qed.

End FixedSize.

Lemma map_copid_mx : forall n r, (copid_mx r)^f = copid_mx r :> 'M_n.
Proof. by move=> n r; rewrite map_mx_sub map_mx1 map_pid_mx. Qed.

Lemma map_mxRM : forall n', GRing.morphism ((map_mx f) n'.+1 n'.+1).
Proof. split; [exact: map_mx_sub | exact: map_mxM | exact: map_mx1]. Qed.

End MapRingMatrix.

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

Lemma diag_mx_comm : forall n' (d e : 'rV[R]_n'.+1),
  GRing.comm (diag_mx d) (diag_mx e).
Proof. move=> n'; exact: diag_mxC. Qed.

Lemma scalar_mxC : forall m n a (A : 'M[R]_(m, n)), A *m a%:M = a%:M *m A.
Proof.
move=> m n a A; apply: trmx_inj.
by rewrite trmx_mul tr_scalar_mx !mul_scalar_mx trmx_scale.
Qed.

Lemma scalar_mx_comm : forall n' a (A : 'M[R]_n'.+1), GRing.comm A a%:M.
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

(* The theory of determinants *)

Lemma determinant_multilinear : forall n (A B C : 'M[R]_n) i0 b c,
    row i0 A = b *m: row i0 B + c *m: row i0 C ->
    row' i0 B = row' i0 A ->
    row' i0 C = row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c; rewrite -[_ + _](row_id 0); move/row_eq=> ABC.
move/row'_eq=> BA; move/row'_eq=> CA.
rewrite !big_distrr -big_split; apply: eq_bigr => s _ /=.
rewrite -!(mulrCA (_ ^+s)) -mulr_addr; congr (_ * _).
rewrite !(bigD1 i0 (_ : predT i0)) //= {}ABC !mxE mulr_addl !mulrA.
by congr (_ * _ + _ * _); apply: eq_bigr => i i0i; rewrite ?BA ?CA.
Qed.

Lemma determinant_alternate : forall n (A : 'M[R]_n) i1 i2,
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

Lemma det_tr : forall n (A : 'M[R]_n), \det A^T = \det A.
Proof.
move=> n A; rewrite /(\det _) (reindex_inj (@invg_inj _)) /=.
apply: eq_bigr => s _ /=; rewrite !odd_permV (reindex_inj (@perm_inj _ s)) /=.
by congr (_ * _); apply: eq_bigr => i _; rewrite mxE permK.
Qed.

Lemma det_perm : forall n (s : 'S_n), \det (perm_mx s) = (-1) ^+ s :> R.
Proof.
move=> n s; rewrite /(\det _) (bigD1 s) //=.
rewrite big1 => [|i _]; last by rewrite /= !mxE eqxx.
rewrite mulr1 big1 ?addr0 => //= t Dst.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (bigD1 i) // mulrCA /= !mxE (negbTE ist) mul0r.
by case/eqP: Dst; apply/permP => i; move/eqP: (Est i).
Qed.

Lemma det1 : forall n, \det (1%:M : 'M[R]_n) = 1.
Proof. by move=> n; rewrite -perm_mx1 det_perm odd_perm1. Qed.

Lemma det_scalemx : forall n x (A : 'M[R]_n), \det (x *m: A) = x ^+ n * \det A.
Proof.
move=> n x A; rewrite big_distrr /=; apply: eq_bigr => s _.
rewrite mulrCA; congr (_ * _).
rewrite -{10}[n]card_ord -prodr_const -big_split /=.
by apply: eq_bigr=> i _; rewrite mxE.
Qed.

Lemma det0 : forall n', \det (0 : 'M[R]_n'.+1) = 0.
Proof. by move=> n'; rewrite -(scale0mx 0) det_scalemx exprS !mul0r. Qed.

Lemma det_scalar : forall n a, \det (a%:M : 'M[R]_n) = a ^+ n.
Proof.
by move=> n a; rewrite -{1}(mulr1 a) -scale_scalar_mx det_scalemx det1 mulr1.
Qed.

Lemma det_scalar1 : forall a, \det (a%:M : 'M[R]_1) = a.
Proof. exact: det_scalar. Qed.

Lemma det_mulmx : forall n (A B : 'M[R]_n), \det (A *m B) = \det A * \det B.
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

Lemma detM : forall n' (A B : 'M[R]_n'.+1), \det (A * B) = \det A * \det B.
Proof. move=> n'; exact: det_mulmx. Qed.

Lemma det_diag : forall n (d : 'rV[R]_n), \det (diag_mx d) = \prod_i d 0 i.
Proof.
move=> n d; rewrite /(\det _) (bigD1 1%g) //= addrC big1 => [|p p1].
  by rewrite add0r odd_perm1 mul1r; apply: eq_bigr => i; rewrite perm1 mxE eqxx.
have{p1}: ~~ perm_on set0 p.
  apply: contra p1; move/subsetP=> p1; apply/eqP; apply/permP=> i.
  by rewrite perm1; apply/eqP; apply/idPn; move/p1; rewrite inE.
case/subsetPn=> i; rewrite !inE eq_sym; move/negbTE=> p_i _.
by rewrite (bigD1 i) //= mulrCA mxE p_i mul0r.
Qed.

(* Laplace expansion lemma *)
Lemma expand_cofactor : forall n (A : 'M[R]_n) i j,
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

Lemma expand_det_row : forall n (A : 'M[R]_n) i0,
  \det A = \sum_j A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
rewrite (partition_big (fun s : 'S_n => s i0) predT) //=.
apply: eq_bigr => j0 _; rewrite expand_cofactor big_distrr /=.
apply: eq_bigr => s; move/eqP=> Dsi0.
rewrite mulrCA (bigID (pred1 i0)) /= big_pred1_eq Dsi0; congr (_ * (_ * _)).
by apply: eq_bigl => i; rewrite eq_sym.
Qed.

Lemma cofactor_tr : forall n (A : 'M[R]_n) i j,
  cofactor A^T i j = cofactor A j i.
Proof.
move=> n A i j; rewrite /cofactor addnC; congr (_ * _).
rewrite -tr_row' -tr_col' det_tr; congr (\det _).
by apply/matrixP=> ? ?; rewrite !mxE.
Qed.

Lemma expand_det_col : forall n (A : 'M[R]_n) j0,
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -det_tr (expand_det_row _ j0).
by apply: eq_bigr => i _; rewrite cofactor_tr mxE.
Qed.

(* Cramer Rule : adjugate on the left *)
Lemma mul_mx_adj : forall n (A : 'M[R]_n), A *m \adj A = (\det A)%:M.
Proof.
move=> n A; apply/matrixP=> i1 i2; rewrite !mxE; case Di: (i1 == i2).
  rewrite (eqP Di) (expand_det_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxE.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxE Di eq_refl.
rewrite -[_ *+ _](determinant_alternate (negbT Di) EBi12) (expand_det_row _ i2).
apply: eq_bigr => j _; rewrite !mxE eq_refl; congr (_ * (_ * _)).
apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => i _.
by rewrite !mxE eq_sym -if_neg neq_lift.
Qed.

Lemma trmx_adj : forall n (A : 'M[R]_n), (\adj A)^T = \adj A^T.
Proof. by move=> n A; apply/matrixP=> i j; rewrite !mxE cofactor_tr. Qed.

(* Cramer rule : adjugate on the right *)
Lemma mul_adj_mx : forall n (A : 'M[R]_n), \adj A *m A = (\det A)%:M.
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

Lemma det_ublock : forall n1 n2 Aul (Aur : 'M[R]_(n1, n2)) Adr,
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

Lemma det_lblock : forall n1 n2 Aul (Adl : 'M[R]_(n2, n1)) Adr,
  \det (block_mx Aul 0 Adl Adr) = \det Aul * \det Adr.
Proof. by move=> *; rewrite -det_tr tr_block_mx trmx0 det_ublock !det_tr. Qed.

End ComMatrix.

(*****************************************************************************)
(********************** Matrix unit ring and inverse marices *****************)
(*****************************************************************************)

Section MatrixInv.

Variables R : comUnitRingType.

Section Defs.

Variable n : nat.

Definition unitmx : pred 'M[R]_n := fun A => GRing.unit (\det A).
Definition invmx A := if A \in unitmx then (\det A)^-1 *m: \adj A else A.

Lemma unitmxE : forall A, (A \in unitmx) = GRing.unit (\det A).
Proof. by []. Qed.

Lemma unitmx1 : 1%:M \in unitmx. Proof. by rewrite unitmxE det1 unitr1. Qed.

Lemma unitmx_perm : forall s, perm_mx s \in unitmx.
Proof. by move=> s; rewrite unitmxE det_perm unitr_exp ?unitr_opp ?unitr1. Qed.

Lemma unitmx_tr : forall A, (A^T \in unitmx) = (A \in unitmx).
Proof. by move=> A; rewrite unitmxE det_tr. Qed.

Lemma mulVmx : {in unitmx, left_inverse 1%:M invmx mulmx}.
Proof.
by move=> A nsA; rewrite /invmx nsA -scalemxAl mul_adj_mx scale_scalar_mx mulVr.
Qed.

Lemma mulmxV : {in unitmx, right_inverse 1%:M invmx mulmx}.
Proof.
by move=> A nsA; rewrite /invmx nsA -scalemxAr mul_mx_adj scale_scalar_mx mulVr.
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
move=> A; case uA: (A \in unitmx); last by rewrite /invmx uA invr_out ?negbT.
by apply: (mulrI uA); rewrite -det_mulmx mulmxV ?divrr ?det1.
Qed.

Lemma unitmx_inv : forall A, (invmx A \in unitmx) = (A \in unitmx).
Proof. by move=> A; rewrite !unitmxE det_inv unitr_inv. Qed.

Lemma trmx_inv : forall A : 'M_n, (invmx A)^T = invmx (A^T).
Proof.
by move=> A; rewrite (fun_if trmx) trmx_scale trmx_adj -unitmx_tr -det_tr.
Qed.

Lemma invmxK : involutive invmx.
Proof.
move=> A; case uA : (A \in unitmx); last by rewrite /invmx !uA.
by apply: (can_inj (mulKVmx uA)); rewrite mulVmx // mulmxV ?unitmx_inv.
Qed.

Lemma mulmx1_unit : forall A B, A *m B = 1%:M -> A \in unitmx /\ B \in unitmx.
Proof.
by move=> A B AB1; apply/andP; rewrite -unitr_mul -det_mulmx AB1 det1 unitr1.
Qed.

Lemma intro_unitmx : forall A B, B *m A = 1%:M /\ A *m B = 1%:M -> unitmx A.
Proof. by move=> A B [_]; case/mulmx1_unit. Qed.

Lemma invmx_out : {in predC unitmx, invmx =1 id}.
Proof. by move=> A; rewrite inE /= /invmx -if_neg => ->. Qed.

End Defs.

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitRingMixin :=
  UnitRingMixin (@mulVmx n) (@mulmxV n) (@intro_unitmx n) (@invmx_out n).
Canonical Structure matrix_unitRing :=
  Eval hnf in UnitRingType 'M[R]_n matrix_unitRingMixin.

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

(* Finite inversible matrices and the general linear group. *)
Section FinUnitMatrix.

Variables (n : nat) (R : finComUnitRingType).

Canonical Structure matrix_finUnitRingType n' :=
  Eval hnf in [finUnitRingType of 'M[R]_n'.+1].

Definition GLtype of phant R := {unit 'M[R]_n.-1.+1}.

Coercion GLval ph (u : GLtype ph) : 'M[R]_n.-1.+1 :=
  let: FinRing.Unit A _ := u in A.

End FinUnitMatrix.

Bind Scope group_scope with GLtype.
Arguments Scope GLval [nat_scope _ _ group_scope].
Prenex Implicits GLval.

Notation "{ ''GL_' n [ R ] }" := (GLtype n (Phant R))
  (at level 0, n at level 2, format "{ ''GL_' n [ R ] }") : type_scope.
Notation "{ ''GL_' n ( p ) }" := {'GL_n['F_p]}
  (at level 0, n at level 2, p at level 10,
    format "{ ''GL_' n ( p ) }") : type_scope.

Section GL_unit.

Variables (n : nat) (R : finComUnitRingType).

Canonical Structure GL_subType := [subType for @GLval n _ (Phant R)].
Definition GL_eqMixin := Eval hnf in [eqMixin of {'GL_n[R]} by <:].
Canonical Structure GL_eqType := Eval hnf in EqType {'GL_n[R]} GL_eqMixin.
Canonical Structure GL_choiceType := Eval hnf in [choiceType of {'GL_n[R]}].
Canonical Structure GL_countType := Eval hnf in [countType of {'GL_n[R]}].
Canonical Structure GL_subCountType :=
  Eval hnf in [subCountType of {'GL_n[R]}].
Canonical Structure GL_finType := Eval hnf in [finType of {'GL_n[R]}].
Canonical Structure GL_subFinType := Eval hnf in [subFinType of {'GL_n[R]}].
Canonical Structure GL_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of {'GL_n[R]}].
Canonical Structure GL_finGroupType :=
  Eval hnf in [finGroupType of {'GL_n[R]}].
Definition GLgroup of phant R := [set: {'GL_n[R]}].
Canonical Structure GLgroup_group ph := Eval hnf in [group of GLgroup ph].

Implicit Types u v : {'GL_n[R]}.

Lemma GL_1E : GLval 1 = 1. Proof. by []. Qed.
Lemma GL_VE : forall u, GLval u^-1 = (GLval u)^-1. Proof. by []. Qed.
Lemma GL_VxE : forall u, GLval u^-1 = invmx u. Proof. by []. Qed.
Lemma GL_ME : forall u v, GLval (u * v) = GLval u * GLval v. Proof. by []. Qed.
Lemma GL_MxE : forall u v, GLval (u * v) = u *m v. Proof. by []. Qed.
Lemma GL_unit : forall u, GRing.unit (GLval u). Proof. exact: valP. Qed.
Lemma GL_unitmx : forall u, val u \in unitmx. Proof. exact: GL_unit. Qed.

Lemma GL_det : forall u, \det u != 0.
Proof.
move=> u; apply: contraL (GL_unitmx u); rewrite unitmxE; move/eqP->.
by rewrite unitr0.
Qed.

End GL_unit.

Notation "''GL_' n [ R ]" := (GLgroup n (Phant R))
  (at level 8, n at level 2, format "''GL_' n [ R ]") : group_scope.
Notation "''GL_' n ( p )" := 'GL_n['F_p]
  (at level 8, n at level 2, p at level 10,
   format "''GL_' n ( p )") : group_scope.
Notation "''GL_' n [ R ]" := (GLgroup_group n (Phant R)) : subgroup_scope.
Notation "''GL_' n ( p )" := (GLgroup_group n (Phant 'F_p)) : subgroup_scope.

(*****************************************************************************)
(****************************** LUP decomposion ******************************)
(*****************************************************************************)

Section CormenLUP.

Variable F : fieldType.

(* Decomposition of the matrix A to P A = L U with *)
(*   - P a permutation matrix                      *)
(*   - L a unipotent lower triangular matrix       *)
(*   - U an upper triangular matrix                *)

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

Lemma cormen_lup_perm : forall n (A : 'M_n.+1), is_perm_mx (cormen_lup A).1.1.
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

(*****************************************************************************)
(******************** Rank and row-space theory ******************************)
(*****************************************************************************)

Section RowSpaceTheory.

Variable F : fieldType.

(* Decomposition with double pivoting; computes the rank, row and column  *)
(* images, kernels, and complements of a matrix.                          *)

Fixpoint emxrank {m n} : 'M[F]_(m, n) -> 'M_m * 'M_n * nat :=
  match m, n return 'M_(m, n) -> 'M_m * 'M_n * nat with
  | _.+1, _.+1 => fun A : 'M_(1 + _, 1 + _) =>
    if pick (fun k => A k.1 k.2 != 0) is Some (i, j) then
      let a := A i j in let A1 := xrow i 0 (xcol j 0 A) in
      let u := ursubmx A1 in let v :=  a^-1 *m: dlsubmx A1 in
      let: (L, U, r) := emxrank (drsubmx A1 - v *m u) in
      (xrow i 0 (block_mx 1 0 v L), xcol j 0 (block_mx a%:M u 0 U), r.+1)
    else (1%:M, 1%:M, 0%N)
  | _, _ => fun _ => (1%:M, 1%:M, 0%N)
  end.

Section Defs.

Variables (m n : nat) (A : 'M[F]_(m, n)).

Definition col_ebase := (emxrank A).1.1.
Definition row_ebase := (emxrank A).1.2.
Definition mxrank := (emxrank A).2.

Definition row_free := mxrank == m.
Definition row_full := mxrank == n.

Definition row_base : 'M_(mxrank, n) := pid_mx mxrank *m row_ebase.
Definition col_base : 'M_(m, mxrank) := col_ebase *m pid_mx mxrank.

Definition complmx : 'M_n := copid_mx mxrank *m row_ebase.
Definition kermx : 'M_m := copid_mx mxrank *m invmx col_ebase.
Definition cokermx : 'M_n := invmx row_ebase *m copid_mx mxrank.

Definition pinvmx : 'M_(n, m) :=
  invmx row_ebase *m pid_mx mxrank *m invmx col_ebase.

End Defs.

Arguments Scope mxrank [nat_scope nat_scope matrix_set_scope].
Local Notation "\rank A" := (mxrank A) : nat_scope.
Arguments Scope complmx [nat_scope nat_scope matrix_set_scope].
Local Notation "A ^C" := (complmx A) : matrix_set_scope.

Let mxopE : forall k opty (op : forall m : nat, opty m) m1,
  (let f := let: tt := k in fun m => op m in f) m1 = op m1.
Proof. by case. Qed.

Definition subsetmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  A *m cokermx B == 0.
Fact subsetmx_key : unit. Proof. by []. Qed.
Definition subsetmx := let: tt := subsetmx_key in subsetmx_def.
Arguments Scope subsetmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits subsetmx.
Local Notation "A <= B" := (subsetmx A B) : matrix_set_scope.
Local Notation "A <= B <= C" := ((A <= B) && (B <= C))%MS : matrix_set_scope.
Local Notation "A == B" := (A <= B <= A)%MS : matrix_set_scope.

Definition eqmx m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  prod (\rank A = \rank B)
       (forall m3 (C : 'M_(m3, n)),
            ((A <= C) = (B <= C)) * ((C <= A) = (C <= B)))%MS.
Arguments Scope eqmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Local Notation "A :=: B" := (eqmx A B) : matrix_set_scope.

(* The choice witness for genmx is row_base padded with null rows. *)
Definition genmx_witness m n (A : 'M_(m, n)) : 'M_n :=
  pid_mx (\rank A) *m row_ebase A.
Definition genmx_def m n (A : 'M_(m, n)) :=
  choose (fun B => B == A)%MS (genmx_witness A).
Fact genmx_key : unit. Proof. by []. Qed.
Definition genmx := let: tt := genmx_key in genmx_def.
Local Notation "<< A >>" := (genmx A) : matrix_set_scope.

(* The setwise sum is tweaked so that 0 is a strict identity element for      *)
(* square matrices, because this lets us use the bigops component. As a       *)
(* result, setwise sum is not quite strictly extensional.                     *)
Let sumsmx_nop m n (A : 'M_(m, n)) := conform_mx <<A>>%MS A.
Definition sumsmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  if A == 0 then sumsmx_nop B else if B == 0 then sumsmx_nop A else
  <<col_mx A B>>%MS.
Fact sumsmx_key : unit. Proof. by []. Qed.
Definition sumsmx := let: tt := sumsmx_key in sumsmx_def.
Arguments Scope sumsmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits sumsmx.
Local Notation "A + B" := (sumsmx A B) : matrix_set_scope.
Local Notation "\sum_ ( i | P ) B" := (\big[sumsmx/0]_(i | P) B%MS)
  : matrix_set_scope.

(* The set intersection is similarly biased so that the identity matrix is a  *)
(* strict identity. This is somewhat more delicate than for the sum, because  *)
(* the test for the identity is non-extensional. This forces us to actually   *)
(* bias the choice operator so that it does not accidentally map an           *)
(* intersection of non-identity matrices to 1%:M; this would spoil            *)
(* associativity: if B :&: C = 1%:M but B and C are not identity, then for a  *)
(* square matrix A we have A :&: (B :&: C) = A != (A :&: B) :&: C in general. *)
(* To complicate matters there may not be a square non-singular matrix        *)
(* different than 1%:M, since we could be dealing with 'M['F_2]_1. We         *)
(* sidestep the issue by making all non-square row-full matrices identities,  *)
(* and choosing a normal representative that preserves the capmx_id property. *)
(* Thus A :&: B = 1%:M iff A and B are both identities, and this suffices for *)
(* showing that associativity is strict.                                      *)
Let capmx_id m n (A : 'M_(m, n)) :=
  if m == n then A == pid_mx n else row_full A.
Let capmx_equivb m n (A : 'M_(m, n)) (B : 'M_n) :=
  (B == A)%MS && (capmx_id B == capmx_id A).
Let capmx_equiv m n (A : 'M_(m, n)) (B : 'M_n) :=
  prod (B :=: A)%MS (capmx_id B = capmx_id A).
Let capmx_witness m n (A : 'M_(m, n)) :=
  if row_full A then conform_mx 1%:M A else <<A>>%MS.
Let capmx_norm m n (A : 'M_(m, n)) :=
  choose (capmx_equivb A) (capmx_witness A).
Let capmx_nop m n (A : 'M_(m, n)) := conform_mx (capmx_norm A) A.
Definition capmx_gen m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  lsubmx (kermx (col_mx A B)) *m A.
Definition capmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  if capmx_id A then capmx_nop B else
  if capmx_id B then capmx_nop A else
  if row_full B then capmx_norm A else capmx_norm (capmx_gen A B).
Fact capmx_key : unit. Proof. by []. Qed.
Definition capmx := let: tt := capmx_key in capmx_def.
Arguments Scope capmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits capmx.
Local Notation "A :&: B" := (capmx A B) : matrix_set_scope.
Local Notation "\bigcap_ ( i | P ) B" := (\big[capmx/1%:M]_(i | P) B)
  : matrix_set_scope.

Definition diffmx_def m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)) :=
  <<capmx_gen A (capmx_gen A B)^C>>%MS.
Fact diffmx_key : unit. Proof. by []. Qed.
Definition diffmx := let: tt := diffmx_key in diffmx_def.
Arguments Scope diffmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits diffmx.
Local Notation "A :\: B" := (diffmx A B) : matrix_set_scope.

Lemma rank_leq_row : forall m n (A : 'M_(m, n)), \rank A <= m.
Proof.
rewrite /mxrank; elim=> [|m IHm] [|n] //= A; case: pickP=> [[i j] _|] //=.
by move: (_ - _) => B; case: emxrank (IHm _ B) => [[L U] r] /=.
Qed.

Lemma row_leq_rank : forall m n (A : 'M_(m, n)), (m <= \rank A) = row_free A.
Proof. by move=> m n A; rewrite /row_free eqn_leq rank_leq_row. Qed.

Lemma rank_leq_col : forall m n (A : 'M_(m, n)), \rank A <= n.
Proof.
rewrite /mxrank; elim=> [|m IHm] [|n] //= A; case: pickP=> [[i j] _|] //=.
by move: (_ - _) => B; case: emxrank (IHm _ B) => [[L U] r] /=.
Qed.

Lemma col_leq_rank : forall m n (A : 'M_(m, n)), (n <= \rank A) = row_full A.
Proof. by move=> m n A; rewrite /row_full eqn_leq rank_leq_col. Qed.

Let unitmx1F := @unitmx1 F.
Lemma row_ebase_unit : forall m n (A : 'M_(m, n)), row_ebase A \in unitmx.
Proof.
rewrite /row_ebase; elim=> [|m IHm] [|n] //= A.
case: pickP => [[i j] /= nzAij | //=]; move: (_ - _) => B.
case: emxrank (IHm _ B) => [[L U] r] /= uU.
rewrite unitmxE xcolE det_mulmx (@det_ublock _ 1) det_scalar1 !unitr_mul.
by rewrite unitfE nzAij -!unitmxE uU  unitmx_perm.
Qed.

Lemma col_ebase_unit : forall m n (A : 'M_(m, n)), col_ebase A \in unitmx.
Proof.
rewrite /col_ebase; elim=> [|m IHm] [|n] //= A; case: pickP => [[i j] _|] //=.
move: (_ - _) => B; case: emxrank (IHm _ B) => [[L U] r] /= uL.
rewrite unitmxE xrowE det_mulmx (@det_lblock _ 1) det1 mul1r unitr_mul.
by rewrite -unitmxE unitmx_perm.
Qed.
Hint Resolve rank_leq_row rank_leq_col row_ebase_unit col_ebase_unit.

Lemma mulmx_ebase : forall m n (A : 'M_(m, n)),
  col_ebase A *m pid_mx (\rank A) *m row_ebase A = A.
Proof.
rewrite /col_ebase /row_ebase /mxrank.
elim=> [n A | m IHm]; first by rewrite [A]flatmx0 [_ *m _]flatmx0.
case=> [A | n]; first by rewrite [_ *m _]thinmx0 [A]thinmx0.
rewrite -(add1n m) -?(add1n n) => A /=.
case: pickP => [[i0 j0] | A0] /=; last first.
  apply/matrixP=> i j; rewrite pid_mx_0 mulmx0 mul0mx mxE.
  by move/eqP: (A0 (i, j)).
set a := A i0 j0 => nz_a; set A1 := xrow _ _ _.
set u := ursubmx _; set v := _ *m: _; set B : 'M_(m, n) := _ -  _.
move: (rank_leq_col B) (rank_leq_row B) {IHm}(IHm n B); rewrite /mxrank.
case: (emxrank B) => [[L U] r] /= r_m r_n defB.
have ->: pid_mx (1 + r) = block_mx 1 0 0 (pid_mx r) :> 'M[F]_(1 + m, 1 + n).
  rewrite -(subnKC r_m) -(subnKC r_n) pid_mx_block -col_mx0 -row_mx0.
  by rewrite block_mxA castmx_id col_mx0 row_mx0 -scalar_mx_block -pid_mx_block.
rewrite xcolE xrowE  mulmxA -xcolE -!mulmxA.
rewrite !(addr0, add0r, mulmx0, mul0mx, mulmx_block, mul1mx) mulmxA defB.
rewrite addrC subrK mul_mx_scalar scalemxA divff // scale1mx.
have ->: a%:M = ulsubmx A1 by rewrite [_ A1]mx11_scalar !mxE !lshift0 !tpermR.
rewrite submxK /A1 xrowE !xcolE -!mulmxA mulmxA -!perm_mxM !tperm2 !perm_mx1.
by rewrite mulmx1 mul1mx.
Qed.

Lemma mulmx_base : forall m n (A : 'M_(m, n)), col_base A *m row_base A = A.
Proof.
by move=> m n A; rewrite mulmxA -[col_base A *m _]mulmxA pid_mx_id ?mulmx_ebase.
Qed.

Lemma mulmx1_min_rank : forall r m n (A : 'M_(m, n)) M N,
  M *m A *m N = 1%:M :> 'M_r -> r <= \rank A.
Proof.
move=> r m n A M N.
by rewrite -{1}(mulmx_base A) mulmxA -mulmxA; move/mulmx1_min.
Qed.
Implicit Arguments mulmx1_min_rank [r m n A].

Lemma mulmx_max_rank : forall r m n (M : 'M_(m, r)) (N : 'M_(r, n)),
  \rank (M *m N) <= r.
Proof.
move=> r m n M N; set MN := M *m N; set rMN := \rank _.
pose L : 'M_(rMN, m) := pid_mx rMN *m invmx (col_ebase MN).
pose U : 'M_(n, rMN) := invmx (row_ebase MN) *m pid_mx rMN.
suffices: L *m M *m (N *m U) = 1%:M by exact: mulmx1_min.
rewrite mulmxA -(mulmxA L) -[M *m N]mulmx_ebase -/MN.
by rewrite !mulmxA mulmxKV // mulmxK // !pid_mx_id /rMN ?pid_mx_1.
Qed.
Implicit Arguments mulmx_max_rank [r m n].

Lemma mxrank_tr : forall m n (A : 'M_(m, n)), \rank A^T = \rank A.
Proof.
move=> m n A; apply/eqP; rewrite eqn_leq -{3}[A]trmxK.
by rewrite -{1}(mulmx_base A) -{1}(mulmx_base A^T) !trmx_mul !mulmx_max_rank.
Qed.

Lemma mxrank_add : forall m n (A B : 'M_(m, n)),
  \rank (A + B)%R <= \rank A + \rank B.
Proof.
move=> m n A B; rewrite -{1}(mulmx_base A) -{1}(mulmx_base B) -mul_row_col.
exact: mulmx_max_rank.
Qed.

Lemma mxrankM_maxl : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank (A *m B) <= \rank A.
Proof.
by move=> m n p A B; rewrite -{1}(mulmx_base A) -mulmxA mulmx_max_rank.
Qed.

Lemma mxrankM_maxr : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank (A *m B) <= \rank B.
Proof.
by move=> m n p A B; rewrite -mxrank_tr -(mxrank_tr B) trmx_mul mxrankM_maxl.
Qed.

Lemma mxrank_scale : forall m n a (A : 'M_(m, n)),
  \rank (a *m: A) <= \rank A.
Proof. by move=> m n a A; rewrite -mul_scalar_mx mxrankM_maxr. Qed.

Lemma mxrank_scale_nz : forall m n a (A : 'M_(m, n)),
  a != 0 -> \rank (a *m: A) = \rank A.
Proof.
move=> m n a A nza; apply/eqP; rewrite eqn_leq -{3}[A]scale1mx -(mulVf nza).
by rewrite -scalemxA !mxrank_scale.
Qed.

Lemma mxrank_opp : forall m n (A : 'M_(m, n)), \rank (- A) = \rank A.
Proof.
by move=> m n A; rewrite -scaleN1mx mxrank_scale_nz // oppr_eq0 oner_eq0.
Qed.

Lemma mxrank0 : forall m n, \rank (0 : 'M_(m, n)) = 0%N.
Proof.
by move=> m n; apply/eqP; rewrite -leqn0 -(@mulmx0 _ m 0 n 0) mulmx_max_rank.
Qed.

Lemma mxrank_eq0 : forall m n (A : 'M_(m, n)), (\rank A == 0%N) = (A == 0).
Proof.
move=> m n A; apply/eqP/eqP=> [rA0 | ->{A}]; last exact: mxrank0.
move: (col_base A) (row_base A) (mulmx_base A); rewrite rA0 => Ac Ar <-.
by rewrite [Ac]thinmx0 mul0mx.
Qed.

Lemma mulmx_coker : forall m n (A : 'M_(m, n)), A *m cokermx A = 0.
Proof.
move=> m n A; rewrite -{1}[A]mulmx_ebase -!mulmxA mulKVmx //.
by rewrite mul_pid_mx_copid ?mulmx0.
Qed.

Lemma subsetmxE : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS = (A *m cokermx B == 0).
Proof. by move=> m1; rewrite mxopE. Qed.

Lemma mulmxKpV : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> A *m pinvmx B *m B = A.
Proof.
move=> m n p A B; rewrite subsetmxE !mulmxA mulmx_subr mulmx1 subr_eq0.
move/eqP=> defA; rewrite -{4}[B]mulmx_ebase -!mulmxA mulKmx //.
by rewrite (mulmxA (pid_mx _)) pid_mx_id // !mulmxA -{}defA mulmxKV.
Qed.

Lemma subsetmxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (exists D, A = D *m B) (A <= B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [|[D ->]].
  by move/mulmxKpV; exists (A *m pinvmx B).
by rewrite subsetmxE -mulmxA mulmx_coker mulmx0.
Qed.
Implicit Arguments subsetmxP [m1 m2 n A B].

Lemma subsetmx_refl : forall m n (A : 'M_(m, n)), (A <= A)%MS.
Proof. by move=> m n A; rewrite subsetmxE mulmx_coker. Qed.
Hint Resolve subsetmx_refl.

Lemma subsetmxMl : forall m n p (D : 'M_(m, n)) (A : 'M_(n, p)),
  (D *m A <= A)%MS.
Proof. by move=> m n p D A; rewrite subsetmxE -mulmxA mulmx_coker mulmx0. Qed.

Lemma subsetmxMr : forall m1 m2 n p,
                   forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  (A <= B)%MS -> (A *m C <= B *m C)%MS.
Proof.
by move=> m1 m2 n p A B C; case/subsetmxP=> D ->; rewrite -mulmxA subsetmxMl.
Qed.

Lemma subsetmxMtrans : forall m n1 n2 p (C : 'M_(m, n1)) A (B : 'M_(n2, p)),
  (A <= B -> C *m A <= B)%MS.
Proof.
by move=> m n1 n2 p C A B; case/subsetmxP=> D ->; rewrite mulmxA subsetmxMl.
Qed.

Lemma subsetmx_trans : forall m1 m2 m3 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= B -> B <= C -> A <= C)%MS.
Proof.
move=> m1 m2 m3 n A B C; case/subsetmxP=> D ->{A}; exact: subsetmxMtrans.
Qed.

Lemma subset0mx : forall m1 m2 n (A : 'M_(m2, n)),
  ((0 : 'M_(m1, n)) <= A)%MS.
Proof. by move=> m1 m2 n A; rewrite subsetmxE mul0mx. Qed.

Lemma subsetmx0null : forall m1 m2 n (A : 'M[F]_(m1, n)),
  (A <= (0 : 'M_(m2, n)))%MS -> A = 0.
Proof. by move=> m1 m2 n A; case/subsetmxP=> D; rewrite mulmx0. Qed.

Lemma subsetmx0 : forall m n (A : 'M_(m, n)), (A <= (0 : 'M_n))%MS = (A == 0).
Proof.
move=> m n A; apply/idP/eqP=> [|->]; [exact: subsetmx0null | exact: subset0mx].
Qed.

Lemma subsetmx_add : forall m1 m2 n,
                  forall (A : 'M_(m1, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)),
  (A <= C)%MS -> (B <= C)%MS -> ((A + B)%R <= C)%MS.
Proof.
move=> m1 m2 n A B C; case/subsetmxP=> A' ->; case/subsetmxP=> B' ->.
by rewrite -mulmx_addl subsetmxMl.
Qed.

Lemma subsetmx_sum : forall m1 m2 n (B : 'M_(m2, n)),
                     forall I r (P : pred I) (A_ : I -> 'M_(m1, n)),
  (forall i, P i -> A_ i <= B)%MS -> ((\sum_(i <- r | P i) A_ i)%R <= B)%MS.
Proof.
move=> m1 m2 n B; pose leB (A : 'M_(m1, n)) := (A <= B)%MS.
apply: (@big_prop _ leB) => [| A1 A2]; [exact: subset0mx | exact: subsetmx_add].
Qed.

Lemma subsetmx_scale : forall m1 m2 n a (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> (a *m: A <= B)%MS.
Proof.
by move=> m1 m2 n a A B; case/subsetmxP=> A' ->; rewrite scalemxAl subsetmxMl.
Qed.

Lemma row_sub : forall m n i (A : 'M_(m, n)), (row i A <= A)%MS.
Proof. by move=> m n i A; rewrite rowE subsetmxMl. Qed.

Lemma eq_row_sub : forall m n v (A : 'M_(m, n)) i, row i A = v -> (v <= A)%MS.
Proof. by move=> m n v A i <-; rewrite row_sub. Qed.

Lemma row_subP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (forall i, row i A <= B)%MS (A <= B)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [sAB i|sAB].
  by apply: subsetmx_trans sAB; exact: row_sub.
rewrite subsetmxE; apply/eqP; apply/row_matrixP=> i; apply/eqP.
by rewrite row_mul row0 -subsetmxE.
Qed.
Implicit Arguments row_subP [m1 m2 n A B].

Lemma row_subPn : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (exists i, ~~ (row i A <= B)%MS) (~~ (A <= B)%MS).
Proof.
move=> m1 m2 n A B; rewrite (sameP row_subP forallP) negb_forall.
exact: existsP.
Qed.

Lemma sub_rVP : forall n (u v : 'rV_n),
  reflect (exists a, u = a *m: v) (u <= v)%MS.
Proof.
move=> n u v; apply: (iffP subsetmxP) => [[w ->] | [a ->]].
  by exists (w 0 0); rewrite -mul_scalar_mx -mx11_scalar.
by exists a%:M; rewrite mul_scalar_mx.
Qed.

Lemma rowV0Pn : forall m n (A : 'M_(m, n)),
  reflect (exists2 v : 'rV_n, v <= A & v != 0)%MS (A != 0).
Proof.
move=> m n A; rewrite -subsetmx0; apply: (iffP idP) => [| [v svA]]; last first.
  by rewrite -subsetmx0; exact: contra (subsetmx_trans _).
by case/row_subPn=> i; rewrite subsetmx0; exists (row i A); rewrite ?row_sub.
Qed.

Lemma rowV0P : forall m n (A : 'M_(m, n)),
  reflect (forall v : 'rV_n, v <= A -> v = 0)%MS (A == 0).
Proof.
move=> m n A; rewrite -[A == 0]negbK; case: rowV0Pn => IH.
  by right; case: IH => v svA nzv IH; case/eqP: nzv; exact: IH.
by left=> v svA; apply/eqP; apply/idPn=> nzv; case: IH; exists v.
Qed.  

Lemma subsetmx_full : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  row_full B -> (A <= B)%MS.
Proof.
move=> m1 m2 n A B; rewrite subsetmxE /cokermx; move/eqnP->.
by rewrite /copid_mx pid_mx_1 subrr !mulmx0.
Qed.

Lemma row_fullP : forall m n (A : 'M_(m, n)),
  reflect (exists B, B *m A = 1%:M) (row_full A).
Proof.
move=> m n A; apply: (iffP idP) => [Afull | [B kA]].
  by exists (1%:M *m pinvmx A); apply: mulmxKpV (subsetmx_full _ Afull).
by rewrite [_ A]eqn_leq rank_leq_col (mulmx1_min_rank B 1%:M) ?mulmx1.
Qed.
Implicit Arguments row_fullP [m n A].

Lemma row_freeP : forall m n (A : 'M_(m, n)),
  reflect (exists B, A *m B = 1%:M) (row_free A).
Proof.
move=> m n A; rewrite /row_free -mxrank_tr.
apply: (iffP row_fullP) => [] [B kA];
  by exists B^T; rewrite -trmx1 -kA trmx_mul ?trmxK.
Qed.

Lemma row_free_unit : forall n (A : 'M_n), row_free A = (A \in unitmx).
Proof.
move=> n A; apply/row_fullP/idP=> [[A'] | uA]; first by case/mulmx1_unit.
by exists (invmx A); rewrite mulVmx.
Qed.

Lemma row_full_unit : forall n (A : 'M_n), row_full A = (A \in unitmx).
Proof. exact: row_free_unit. Qed.
  
Lemma mxrank_unit : forall n (A : 'M_n), A \in unitmx -> \rank A = n.
Proof. by move=> n A; rewrite -row_full_unit; move/eqnP. Qed.

Lemma mxrank1 : forall n, \rank (1%:M : 'M_n) = n.
Proof. move=> n; apply: mxrank_unit; exact: unitmx1. Qed.

Lemma mxrankS : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> \rank A <= \rank B.
Proof. by move=> m1 m2 n A B; case/subsetmxP=> D ->; rewrite mxrankM_maxr. Qed.

Lemma subsetmx1 : forall m n (A : 'M[F]_(m, n)), (A <= 1%:M)%MS.
Proof. by move=> m n A; rewrite subsetmx_full // row_full_unit unitmx1. Qed.

Lemma subset1mx : forall m n (A : 'M[F]_(m, n)), (1%:M <= A)%MS = row_full A.
Proof.
move=> m n A; apply/idP/idP; last exact: subsetmx_full.
by move/mxrankS; rewrite mxrank1 col_leq_rank.
Qed.

Lemma eqmxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :=: B)%MS (A == B)%MS.
Proof.
move=> m1 m2 n A B.
apply: (iffP andP) => [[sAB sBA] | eqAB]; last by rewrite !eqAB.
split=> [|m3 C]; first by apply/eqP; rewrite eqn_leq !mxrankS.
split; first by apply/idP/idP; exact: subsetmx_trans.
by apply/idP/idP=> sC; exact: subsetmx_trans sC _.
Qed.

Lemma eqmx_refl : forall m1 n (A : 'M_(m1, n)), (A :=: A)%MS.
Proof. by []. Qed.

Lemma eqmx_sym : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B)%MS -> (B :=: A)%MS.
Proof. by move=> m1 m2 n A B eqAB; split=> [|m3 C]; rewrite !eqAB. Qed.

Lemma eqmx_trans : forall m1 m2 m3 n,
                   forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A :=: B)%MS -> (B :=: C)%MS -> (A :=: C)%MS.
Proof.
by move=> m1 m2 m3 n A B C eqAB eqBC; split=> [|m4 D]; rewrite !eqAB !eqBC.
Qed.

Lemma eqmx_rank : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A == B)%MS -> \rank A = \rank B.
Proof. by move=> m1 m2 n A B; move/eqmxP->. Qed.

Lemma eqmxMr : forall m1 m2 n p,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  (A :=: B)%MS -> (A *m C :=: B *m C)%MS.
Proof.
by move=> m1 m2 n p A B C eqAB; apply/eqmxP; rewrite !subsetmxMr ?eqAB.
Qed.

Lemma eqmxMfull : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  row_full A -> (A *m B :=: B)%MS.
Proof.
move=> m n p A B; case/row_fullP=> A' A'A; apply/eqmxP; rewrite subsetmxMl /=.
by apply/subsetmxP; exists A'; rewrite mulmxA A'A mul1mx.
Qed.

Lemma eqmx0 : forall m n, ((0 : 'M[F]_(m, n)) :=: (0 : 'M_n))%MS.
Proof. by move=> m n; apply/eqmxP; rewrite !subset0mx. Qed.

Lemma eqmx_scale : forall m n a (A : 'M_(m, n)), a != 0 -> (a *m: A :=: A)%MS.
Proof.
move=> m n a A nz_a; apply/eqmxP; rewrite subsetmx_scale //.
by rewrite -{1}[A]scale1mx -(mulVf nz_a) -scalemxA subsetmx_scale.
Qed.

Lemma eqmx_opp : forall m n (A : 'M_(m, n)), (- A :=: A)%MS.
Proof.
move=> m n A; rewrite -scaleN1mx; apply: eqmx_scale => //.
by rewrite oppr_eq0 oner_eq0.
Qed.

Lemma subsetmxMfree : forall m1 m2 n p,
                     forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  row_free C -> (A *m C <= B *m C)%MS = (A <= B)%MS.
Proof.
move=> m1 m2 n p A B C; case/row_freeP=> C' C_C'_1.
apply/idP/idP=> sAB; last exact: subsetmxMr.
by rewrite -[A]mulmx1 -[B]mulmx1 -C_C'_1 !mulmxA subsetmxMr.
Qed.

Lemma eqmxMfree : forall m1 m2 n p,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  row_free C -> (A *m C :=: B *m C)%MS -> (A :=: B)%MS.
Proof.
move=> m1 m2 n p A B C Cfree eqAB; apply/eqmxP; move/eqmxP: eqAB.
by rewrite !subsetmxMfree.
Qed.

Lemma mxrankMfree : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  row_free B -> \rank (A *m B) = \rank A.
Proof.
move=> m n p A B Bfree.
by rewrite -mxrank_tr trmx_mul eqmxMfull /row_full mxrank_tr.
Qed.

Lemma eq_row_base : forall m n (A : 'M_(m, n)), (row_base A :=: A)%MS.
Proof.
move=> m n A; apply/eqmxP; apply/andP; split; apply/subsetmxP.
  exists (pid_mx (\rank A) *m invmx (col_ebase A)).
  by rewrite -{8}[A]mulmx_ebase !mulmxA mulmxKV // pid_mx_id.
exists (col_ebase A *m pid_mx (\rank A)).
by rewrite mulmxA -(mulmxA _ _ (pid_mx _)) pid_mx_id // mulmx_ebase.
Qed.

Let genmx_witnessP : forall m n (A : 'M_(m, n)), (genmx_witness A == A)%MS.
Proof.
move=> m n A; apply/andP; split; apply/subsetmxP.
  exists (pid_mx (\rank A) *m invmx (col_ebase A)).
  by rewrite -{4}[A]mulmx_ebase !mulmxA mulmxKV // pid_mx_id.
exists (col_ebase A *m pid_mx (\rank A)).
by rewrite mulmxA -(mulmxA _ _ (pid_mx _)) pid_mx_id // mulmx_ebase.
Qed.

Lemma genmxE : forall m n (A : 'M_(m, n)), (<<A>> :=: A)%MS.
Proof.
move=> m n A; rewrite mxopE; set eqA := fun _ => _; apply/eqmxP.
by rewrite [_ && _](@chooseP _ eqA) //; exact: genmx_witnessP.
Qed.

Lemma gen_eqmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B -> <<A>> = <<B>>)%MS.
Proof.
move=> m1 m2 n A B eqAB; rewrite ![@genmx _]mxopE.
pose eqABr := (genmx_witnessP, eqAB).
by apply: etrans (choose_id _ _) (eq_choose _ _) => [||C]; rewrite !eqABr.
Qed.

Lemma genmxP : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (<<A>> = <<B>>)%MS (<<A>> == <<B>>)%MS.
Proof.
move=> m1 m2 n A B; apply: (iffP idP) => [|->]; last exact/andP.
by rewrite !genmxE; move/eqmxP; exact: gen_eqmx.
Qed.

Lemma genmx0 : forall m n, <<0 : 'M_(m, n)>>%MS = 0.
Proof. by move=> m n; apply/eqP; rewrite -subsetmx0 genmxE subset0mx. Qed.

Lemma genmx_id : forall m n (A : 'M_(m, n)), (<<<<A>>>> = <<A>>)%MS.
Proof. by move=> m n A; apply: gen_eqmx; exact: genmxE. Qed.

Lemma row_base_free : forall m n (A : 'M_(m, n)), row_free (row_base A).
Proof. by move=> m n A; apply/eqnP; rewrite eq_row_base. Qed.

Lemma mxrank_gen : forall m n (A : 'M_(m, n)), \rank <<A>>%MS = \rank A.
Proof. by move=> m n A; rewrite genmxE. Qed.

Lemma col_base_full : forall m n (A : 'M_(m, n)), row_full (col_base A).
Proof.
move=> m n A; apply/row_fullP.
exists (pid_mx (\rank A) *m invmx (col_ebase A)).
by rewrite !mulmxA mulmxKV // pid_mx_id // pid_mx_1.
Qed.
Hint Resolve row_base_free col_base_full.

Lemma mxrank_leqif_sup : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> \rank A <= \rank B ?= iff (B <= A)%MS.
Proof.
move=> m1 m2 n A B sAB; split; first by rewrite mxrankS.
apply/idP/idP=> [| sBA]; last by rewrite eqn_leq !mxrankS.
case/subsetmxP: sAB => D ->; rewrite -{-2}(mulmx_base B) mulmxA.
rewrite mxrankMfree //; case/row_fullP=> E kE.
by rewrite -{1}[row_base B]mul1mx -kE -(mulmxA E) (mulmxA _ E) subsetmxMl.
Qed.

Lemma mxrank_leqif_eq : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A <= B)%MS -> \rank A <= \rank B ?= iff (A == B)%MS.
Proof. by move=> m1 m2 n A B sAB; rewrite sAB; exact: mxrank_leqif_sup. Qed.

Lemma eqmx_cast : forall m1 m2 n (A : 'M_(m1, n)) e,
  ((castmx e A : 'M_(m2, n)) :=: A)%MS.
Proof. by move=> m1 m2 n A [e]; case: m2 / e A => A e; rewrite castmx_id. Qed.

Lemma eqmx_conform : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (conform_mx A B :=: A \/ conform_mx A B :=: B)%MS.
Proof.
move=> m1 m2 n A; case: (eqVneq m2 m1) => [-> | neqm12] B.
  by right; rewrite conform_mx_id.
by left; rewrite nonconform_mx ?neqm12.
Qed.

Let eqmx_sum_nop : forall m n (A : 'M_(m, n)), (sumsmx_nop A :=: A)%MS.
Proof.
move=> m n A; case: (eqmx_conform <<A>>%MS A) => // eq_id_gen.
exact: eqmx_trans (genmxE A).
Qed.

Section SumsmxSub.

Variable (m1 m2 n : nat) (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)).

Lemma col_mx_sub : forall m3 (C : 'M_(m3, n)),
  (col_mx A B <= C)%MS = (A <= C)%MS && (B <= C)%MS.
Proof.
move=> m3 C; rewrite !subsetmxE mul_col_mx -col_mx0.
by apply/eqP/andP; [case/eq_col_mx=> -> -> | case; do 2!move/eqP->].
Qed.

Lemma sumsmxE : (A + B :=: col_mx A B)%MS.
Proof.
have:= subsetmx_refl (col_mx A B); rewrite col_mx_sub; case/andP=> sAS sBS.
rewrite mxopE; do 2?case: eqP => [AB0 | _]; last exact: genmxE.
  by apply/eqmxP; rewrite !eqmx_sum_nop sBS col_mx_sub AB0 subset0mx /=.
by apply/eqmxP; rewrite !eqmx_sum_nop sAS col_mx_sub AB0 subset0mx andbT /=.
Qed.

Lemma sumsmx_sub : forall m3 (C : 'M_(m3, n)),
  (A + B <= C)%MS = (A <= C)%MS && (B <= C)%MS.
Proof. by move=> m3 C; rewrite sumsmxE col_mx_sub. Qed.

Lemma sumsmxSl : (A <= A + B)%MS.
Proof. by have:= subsetmx_refl (A + B)%MS; rewrite sumsmx_sub; case/andP. Qed.

Lemma sumsmxSr : (B <= A + B)%MS.
Proof. by have:= subsetmx_refl (A + B)%MS; rewrite sumsmx_sub; case/andP. Qed.

End SumsmxSub.

Lemma sums0mx: forall m1 m2 n (B : 'M_(m2, n)),
  ((0 : 'M_(m1, n)) + B :=: B)%MS.
Proof.
by move=> *; apply/eqmxP; rewrite sumsmx_sub subset0mx sumsmxSr /= andbT.
Qed.

Lemma sumsmx0: forall m1 m2 n (A : 'M_(m1, n)),
  (A + (0 : 'M_(m2, n)) :=: A)%MS.
Proof.
by move=> *; apply/eqmxP; rewrite sumsmx_sub subset0mx sumsmxSl /= !andbT.
Qed.

Let sumsmx_nop_eq0 : forall m n (A : 'M_(m, n)), (sumsmx_nop A == 0) = (A == 0).
Proof. by move=> m n A; rewrite -!subsetmx0 eqmx_sum_nop. Qed.

Let sumsmx_nop0 : forall m n, sumsmx_nop (0 : 'M_(m, n)) = 0.
Proof. by move=> m n; apply/eqP; rewrite sumsmx_nop_eq0. Qed.

Let sumsmx_nop_id : forall n (A : 'M_n), sumsmx_nop A = A.
Proof. by move=> n A; exact: conform_mx_id. Qed.

Lemma sumsmxC : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A + B = B + A)%MS.
Proof.
move=> m1 m2 n A B; have: (A + B == B + A)%MS.
  by apply/andP; rewrite !sumsmx_sub andbC -sumsmx_sub andbC -sumsmx_sub.
rewrite ![@sumsmx _]mxopE.
case A0: (A == 0); case B0: (B == 0) => //; last by move/genmxP.
by rewrite (eqP A0) (eqP B0) !sumsmx_nop0.
Qed.

Lemma sums0mx_id : forall m1 n (B : 'M_n), ((0 : 'M_(m1, n)) + B)%MS = B.
Proof. by move=> m2 n B; rewrite mxopE eqxx sumsmx_nop_id. Qed.

Lemma sumsmx0_id : forall m2 n (A : 'M_n), (A + (0 : 'M_(m2, n)))%MS = A.
Proof. by move=> m2 n A; rewrite sumsmxC sums0mx_id. Qed.

Lemma sumsmxA : forall m1 m2 m3 n,
                forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A + (B + C) = A + B + C)%MS.
Proof.
move=> m1 m2 m3 n A B C; have: (A + (B + C) :=: A + B + C)%MS.
  by apply/eqmxP; apply/andP; rewrite !sumsmx_sub -andbA andbA -!sumsmx_sub.
rewrite {1 3}[@sumsmx m1]mxopE [@sumsmx n]mxopE !sumsmx_nop_id -!subsetmx0.
rewrite !sumsmx_sub ![@sumsmx _]mxopE -!subsetmx0; move/gen_eqmx.
by do 3!case: (_ <= 0)%MS; rewrite //= !genmx_id.
Qed.

Canonical Structure sumsmx_monoid n :=
  Monoid.Law (@sumsmxA n n n n) (@sums0mx_id n n) (@sumsmx0_id n n).
Canonical Structure sumsmx_comoid n := Monoid.ComLaw (@sumsmxC n n n).

Lemma sumsmxMr : forall m1 m2 n p,
                forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  ((A + B)%MS *m C :=: A *m C + B *m C)%MS.
Proof.
move=> m1 m2 n p A B C; apply/eqmxP; rewrite !sumsmxE -!mul_col_mx.
by rewrite !subsetmxMr ?sumsmxE.
Qed.

Lemma sumsmxS : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A <= C -> B <= D -> A + B <= C + D)%MS.
Proof.
move=> m1 m2 m3 m4 n A B C D sAC sBD.
by rewrite sumsmx_sub {1}sumsmxC !(subsetmx_trans _ (sumsmxSr _ _)).
Qed.

Lemma subsetmx_add_sums : forall m m1 m2 n,
    forall (A : 'M_(m, n)) (B : 'M_(m, n)) (C : 'M_(m1, n)) (D : 'M_(m2, n)),
  (A <= C -> B <= D -> (A + B)%R <= C + D)%MS.
Proof.
move=> m m1 m2 n A B C D sAC; move/(sumsmxS sAC); apply: subsetmx_trans.
by rewrite subsetmx_add ?sumsmxSl ?sumsmxSr.
Qed.

Lemma sums_eqmx : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A :=: C -> B :=: D -> A + B :=: C + D)%MS.
Proof.
move=> m1 m2 m3 m4 n A B C D eqAC eqBD.
by apply/eqmxP; rewrite !sumsmxS ?eqAC ?eqBD.
Qed.

Lemma sub_sumsmxP : forall m1 m2 m3 n,
                    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  reflect (exists2 A', A - A' <= B & A' <= C)%MS (A <= B + C)%MS.
Proof.
move=> m1 m2 m3 n A B C; apply: (iffP idP) => [|[A' sAA'B sA'C]]; last first.
  by rewrite -(subrK A' A) subsetmx_add_sums.
rewrite sumsmxE; case/subsetmxP=> u ->; rewrite -[u]hsubmxK mul_row_col.
by exists (rsubmx u *m C); rewrite ?addrK subsetmxMl.
Qed.
Implicit Arguments sub_sumsmxP [m1 m2 m3 n A B C].

Variable I : finType.
Implicit Type P : pred I.

Lemma bigsumsmx_sup : forall i0 P m n (A : 'M_(m, n)) (B_ : I -> 'M_n),
  P i0 -> (A <= B_ i0)%MS -> (A <= \sum_(i | P i) B_ i)%MS.
Proof.
move=> i0 P m n A B_ Pi0 sAB; apply: subsetmx_trans sAB _.
by rewrite (bigD1 i0) // sumsmxSl.
Qed.
Implicit Arguments bigsumsmx_sup [P m n A B_].

Lemma bigsumsmx_subP : forall P m n (A_ : I -> 'M_n) (B : 'M_(m, n)),
  reflect (forall i, P i -> A_ i <= B)%MS (\sum_(i | P i) A_ i <= B)%MS.
Proof.
move=> P m n A_ B; apply: (iffP idP) => [sAB i Pi | sAB].
  by apply: subsetmx_trans sAB; apply: bigsumsmx_sup Pi _.
by apply big_prop => // [|A1 A2 sA1B]; rewrite ?subset0mx // sumsmx_sub sA1B.
Qed.

Lemma sub_bigsumsmxP : forall P m n (A : 'M_(m, n)) (B_ : I -> 'M_n),
  reflect (exists C_, A = \sum_(i | P i) C_ i *m B_ i)
          (A <= \sum_(i | P i) B_ i)%MS.
Proof.
move=> P m n A B_; elim: {P}_.+1 {-2}P A (ltnSn #|P|) => // b IHb P A.
case: (pickP P) => [i Pi | P0 _]; last first.
  rewrite big_pred0 // subsetmx0.
  apply: (iffP eqP) => [-> | [C_ ->]]; last by rewrite big_pred0.
  by exists (fun _ => 0); rewrite big_pred0.
rewrite (cardD1x Pi) (bigD1 i) //=; move/IHb=> {b IHb} /= IHi.
apply: (iffP sub_sumsmxP) => [[A'] | [C_]]; last first.
  rewrite (bigD1 i) //=; set A' := \sum_(<- _ | _) _ => ->.
  by exists A'; [rewrite addrK subsetmxMl | apply/IHi; exists C_].
case/subsetmxP=> Ci defCi; case/IHi=> C_ defA' {IHi}.
exists [eta C_ with i |-> Ci]; rewrite (bigD1 i) //= eqxx -defCi.
rewrite addrAC -addrA defA' -sumr_sub big1 ?addr0 // => j /=; case/andP=> _.
by case: eqP => // _ _; rewrite subrr.
Qed.

Lemma rank_pid_mx : forall m n r,
  r <= m -> r <= n -> \rank (pid_mx r : 'M_(m, n)) = r.
Proof.
move=> m n r; do 2!move/subnKC <-; rewrite pid_mx_block block_mxEv row_mx0.
rewrite -sumsmxE sumsmx0 -mxrank_tr tr_row_mx trmx0 trmx1 -sumsmxE sumsmx0.
exact: mxrank1.
Qed.

Lemma rank_copid_mx : forall n r,
  r <= n -> \rank (copid_mx r : 'M_n) = (n - r)%N.
Proof.
move=> n r; move/subnKC <-; rewrite /copid_mx pid_mx_block scalar_mx_block.
rewrite opp_block_mx !oppr0 add_block_mx !addr0 subrr block_mxEv row_mx0.
rewrite -sumsmxE sums0mx -mxrank_tr tr_row_mx trmx0 trmx1.
by rewrite -sumsmxE sums0mx mxrank1 addKn.
Qed.

Lemma mxrank_compl : forall m n (A : 'M_(m, n)), \rank A^C%MS = (n - \rank A)%N.
Proof. by move=> m n A; rewrite mxrankMfree ?row_free_unit ?rank_copid_mx. Qed.

Lemma mxrank_ker : forall m n (A : 'M_(m, n)),
  \rank (kermx A) = (m - \rank A)%N.
Proof.
by move=> m n A; rewrite mxrankMfree ?row_free_unit ?unitmx_inv ?rank_copid_mx.
Qed.

Lemma mxrank_coker : forall m n (A : 'M_(m, n)),
  \rank (cokermx A) = (n - \rank A)%N.
Proof.
by move=> m n A; rewrite eqmxMfull ?row_full_unit ?unitmx_inv ?rank_copid_mx.
Qed.

Lemma mulmx_ker : forall m n (A : 'M_(m, n)), kermx A *m A = 0.
Proof.
move=> m n A; rewrite -{2}[A]mulmx_ebase !mulmxA mulmxKV //.
by rewrite mul_copid_mx_pid ?mul0mx.
Qed.

Lemma mulmxKV_ker : forall m n p (A : 'M_(n, p)) (B : 'M_(m, n)),
  B *m A = 0 -> B *m col_ebase A *m kermx A = B.
Proof.
move=> m n p A B; rewrite mulmxA mulmx_subr mulmx1 mulmx_subl mulmxK //.
rewrite -{1}[A]mulmx_ebase !mulmxA; move/(canRL (mulmxK (row_ebase_unit A))).
rewrite mul0mx // => BA0; apply: (canLR (addrK _)).
by rewrite -(pid_mx_id _ _ n (rank_leq_col A)) mulmxA BA0 !mul0mx addr0.
Qed.

Lemma subsetmx_kerP : forall p m n (A : 'M_(m, n)) (B : 'M_(p, m)),
  reflect (B *m A = 0) (B <= kermx A)%MS.
Proof.
move=> p m n A B; apply: (iffP subsetmxP) => [[D ->]|].
  by rewrite -mulmxA mulmx_ker mulmx0.
by move/mulmxKV_ker; exists (B *m col_ebase A).
Qed.

Lemma det0P : forall n (A : 'M_n),
  reflect (exists2 v : 'rV[F]_n, v != 0 & v *m A = 0) (\det A == 0).
Proof.
move=> n A; rewrite -[_ == _]negbK -unitfE -unitmxE.
apply: (iffP idP) => [| [v n0v vA0]]; last first.
  by apply: contra n0v => uA; rewrite -(mulmxK uA v) vA0 mul0mx.
rewrite -row_free_unit /row_free eqn_leq rank_leq_row -subn_eq0.
rewrite -mxrank_ker mxrank_eq0 -subsetmx0; case/row_subPn=> i.
by exists (row i (kermx A)); rewrite -?subsetmx0 // -row_mul mulmx_ker row0.
Qed.

Lemma mulmx0_rank_max : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  A *m B = 0 -> \rank A + \rank B <= n.
Proof.
move=> m n p A B AB0; rewrite -{3}(subnK (rank_leq_row B)) leq_add2r.
rewrite -mxrank_ker mxrankS //; exact/subsetmx_kerP.
Qed.

Lemma mxrank_Frobenius : forall m n p q (A : 'M_(m, n)) B (C : 'M_(p, q)),
  \rank (A *m B) + \rank (B *m C) <= \rank B + \rank (A *m B *m C).
Proof.
move=> m n p q A B C; rewrite -{2}(mulmx_base (A *m B)) -mulmxA.
rewrite (eqmxMfull _ (col_base_full _)); set C2 := row_base _ *m C.
rewrite -{1}(subnK (rank_leq_row C2)) -(mxrank_ker C2) addnAC leq_add2r. 
rewrite addnC -{1}(mulmx_base B) -mulmxA eqmxMfull //.
set C1 := _ *m C; rewrite -{2}(subnKC (rank_leq_row C1)) leq_add2l -mxrank_ker.
rewrite -(mxrankMfree _ (row_base_free (A *m B))).
have: (row_base (A *m B) <= row_base B)%MS by rewrite !eq_row_base subsetmxMl.
case/subsetmxP=> D defD; rewrite defD mulmxA mxrankMfree ?mxrankS //.
by apply/subsetmx_kerP; rewrite -mulmxA (mulmxA D) -defD -/C2 mulmx_ker.
Qed.

Lemma mxrank_mul_min : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  \rank A + \rank B - n <= \rank (A *m B).
Proof.
move=> m n p A B; have:= mxrank_Frobenius A 1%:M B.
by rewrite mulmx1 mul1mx mxrank1 leq_sub_add.
Qed.

Lemma sumsmx_compl_full : forall m n (A : 'M_(m, n)), row_full (A + A^C)%MS.
Proof.
move=> m n A; rewrite /row_full sumsmxE; apply/row_fullP.
exists (row_mx (pinvmx A) (cokermx A)); rewrite mul_row_col.
rewrite -{2}[A]mulmx_ebase -!mulmxA mulKmx // -mulmx_addr !mulmxA.
by rewrite pid_mx_id ?copid_mx_id // -mulmx_addl addrC subrK mul1mx mulVmx.
Qed.

Lemma sub_capmx_gen : forall m1 m2 m3 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= capmx_gen B C)%MS = (A <= B)%MS && (A <= C)%MS.
Proof.
move=> m1 m2 m3 n A B C; apply/idP/andP=> [sAI | []].
  rewrite !(subsetmx_trans sAI) ?subsetmxMl // /capmx_gen.
   have:= mulmx_ker (col_mx B C); set K := kermx _.
   rewrite -{1}[K]hsubmxK mul_row_col; move/(canRL (addrK _))->.
   by rewrite add0r -mulNmx subsetmxMl.
case/subsetmxP=> B' ->{A}; case/subsetmxP=> C' eqBC'.
have: subsetmx (row_mx B' (- C')) (kermx (col_mx B C)).
  by apply/subsetmx_kerP; rewrite mul_row_col eqBC' mulNmx subrr.
case/subsetmxP=> D; rewrite -[kermx _]hsubmxK mul_mx_row.
by case/eq_row_mx=> -> _; rewrite -mulmxA subsetmxMl.
Qed.

Let capmx_id_eq1 : forall n (A : 'M_n), capmx_id A = (A == 1%:M).
Proof. by move=> A; rewrite /capmx_id eqxx pid_mx_1. Qed.

Let capmx_witnessP : forall m n (A : 'M_(m, n)),
  capmx_equivb A (capmx_witness A).
Proof.
move=> m n A; rewrite /capmx_equivb capmx_id_eq1 /capmx_id /capmx_witness.
rewrite -subset1mx; case s1A: (1%:M <= A)%MS => /=; last first.
  rewrite !genmxE subsetmx_refl /= -negb_add; apply: contra {s1A}(negbT s1A).
  case: eqP => [<- _| _]; first by rewrite genmxE.
  by case: eqP A => //= -> A; move/eqP->; rewrite pid_mx_1.
case: (m =P n) => [-> | ne_mn] in A s1A *.
  by rewrite conform_mx_id subsetmx_refl pid_mx_1 eqxx.
by rewrite nonconform_mx ?subsetmx1 ?s1A ?eqxx //; case: eqP.
Qed.

Let capmx_normP: forall m n (A : 'M_(m, n)), capmx_equiv A (capmx_norm A).
Proof.
move=> m n A; case/andP: (chooseP (capmx_witnessP A)).
by move/eqmxP=> defN; move/eqP.
Qed.

Let capmx_norm_eq : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  capmx_id A = capmx_id B -> (A == B)%MS -> capmx_norm A = capmx_norm B.
Proof.
move=> m1 m2 n A B eqABid; move/eqmxP=> eqAB.
have{eqABid eqAB} eqAB: capmx_equivb A =1 capmx_equivb B.
  by move=> C; rewrite /capmx_equivb eqABid !eqAB.
rewrite {1}/capmx_norm (eq_choose eqAB).
by apply: choose_id; first rewrite -eqAB; exact: capmx_witnessP.
Qed.

Let capmx_nopP : forall m n (A : 'M_(m, n)), capmx_equiv A (capmx_nop A).
Proof.
rewrite /capmx_nop => m n; case: (eqVneq m n) => [-> | ne_mn] A.
  by rewrite conform_mx_id.
rewrite nonconform_mx ?ne_mn //; exact: capmx_normP.
Qed.

Let sub_capmx_id : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  capmx_id B -> (A <= B)%MS.
Proof.
rewrite /capmx_id => m1 m2 n A B idB; apply: {A}subsetmx_trans (subsetmx1 A) _.
case: eqP B idB => [-> | _] B; first by move/eqP->; rewrite pid_mx_1.
by rewrite subset1mx.
Qed.

Let capmx_id_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  capmx_id (A :&: B)%MS = capmx_id A && capmx_id B.
Proof.
move=> m1 m2 n A B; rewrite mxopE -subset1mx.
case idA: (capmx_id A); case idB: (capmx_id B); try by rewrite capmx_nopP.
case s1B: (_ <= B)%MS; first by rewrite capmx_normP.
apply/idP; move/(sub_capmx_id 1%:M).
by rewrite capmx_normP sub_capmx_gen s1B andbF.
Qed.

Let capmx_eq_norm : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  capmx_id A = capmx_id B -> (A :&: B)%MS = capmx_norm (A :&: B)%MS.
Proof.
move=> m1 m2 n A B eqABid; rewrite mxopE -subset1mx {}eqABid.
have norm_id: forall m (C : 'M_(m, n)) (N := capmx_norm C), capmx_norm N = N.
  by move=> m C; apply: capmx_norm_eq; rewrite ?capmx_normP ?andbb.
case idB: (capmx_id B); last by case: ifP; rewrite norm_id.
rewrite /capmx_nop; case: (eqVneq m2 n) => [-> | neqm2n] in B idB *.
  have idN := idB; rewrite -{1}capmx_normP !capmx_id_eq1 in idN idB.
  by rewrite conform_mx_id (eqP idN) (eqP idB).
by rewrite nonconform_mx ?neqm2n ?norm_id.
Qed.

Lemma capmxE : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B :=: capmx_gen A B)%MS.
Proof.
move=> m1 m2 n A B; rewrite mxopE -subset1mx; apply/eqmxP.
have:= subsetmx_refl (capmx_gen A B).
rewrite !sub_capmx_gen; case/andP=> sIA sIB.
case idA: (capmx_id A); first by rewrite !capmx_nopP subsetmx_refl sub_capmx_id.
case idB: (capmx_id B); first by rewrite !capmx_nopP subsetmx_refl sub_capmx_id.
case s1B: (1%:M <= B)%MS; rewrite !capmx_normP ?sub_capmx_gen sIA ?sIB //=.
by rewrite subsetmx_refl (subsetmx_trans (subsetmx1 _)).
Qed.

Lemma capmxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= A)%MS.
Proof. by move=> m1 m2 n A B; rewrite capmxE subsetmxMl. Qed.

Lemma sub_capmx : forall m m1 m2 n,
    forall (A : 'M_(m, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)),
  (A <= B :&: C)%MS = (A <= B)%MS && (A <= C)%MS.
Proof. by move=> m m1 m2 n A B C; rewrite capmxE sub_capmx_gen. Qed.

Lemma capmxC : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B = B :&: A)%MS.
Proof.
move=> m1 m2 n A B; case: (eqVneq (capmx_id A) (capmx_id B)) => [eqAB|].
  rewrite (capmx_eq_norm eqAB) (capmx_eq_norm (esym eqAB)).
  apply: capmx_norm_eq; first by rewrite !capmx_id_cap andbC.
  by apply/andP; split; rewrite !sub_capmx andbC -sub_capmx.
by rewrite negb_eqb !mxopE; move/addbP <-; case: (capmx_id A).
Qed.

Lemma capmxSr : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B <= B)%MS.
Proof. by move=> m1 m2 n A B; rewrite capmxC capmxSl. Qed.

Lemma capmxS : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A <= C -> B <= D -> A :&: B <= C :&: D)%MS.
Proof.
move=> m1 m2 m3 m4 n A B C D sAC sBD; rewrite sub_capmx.
by rewrite {1}capmxC !(subsetmx_trans (capmxSr _ _)).
Qed.

Lemma cap_eqmx : forall m1 m2 m3 m4 n,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) (D : 'M_(m4, n)),
  (A :=: C -> B :=: D -> A :&: B :=: C :&: D)%MS.
Proof.
by move=> m1 m2 m3 m4 n A B C D sAC sBD; apply/eqmxP; rewrite !capmxS ?sAC ?sBD.
Qed.

Lemma capmxMr : forall m1 m2 n p,
    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(n, p)),
  ((A :&: B) *m C <= A *m C :&: B *m C)%MS.
Proof.
by move=> m1 m2 n p A B C; rewrite sub_capmx !subsetmxMr ?capmxSl ?capmxSr.
Qed.

Lemma cap0mx : forall m1 m2 n (A : 'M_(m2, n)), ((0 : 'M_(m1, n)) :&: A)%MS = 0.
Proof. by move=> m1 m2 n A; exact: subsetmx0null (capmxSl _ _). Qed.

Lemma capmx0 : forall m1 m2 n (A : 'M_(m1, n)), (A :&: (0 : 'M_(m2, n)))%MS = 0.
Proof. by move=> m1 m2 n A; exact: subsetmx0null (capmxSr _ _). Qed.

Lemma capmxT : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  row_full B -> (A :&: B :=: A)%MS.
Proof.
move=> m1 m2 n A B; rewrite -subset1mx => s1B; apply/eqmxP.
by rewrite capmxSl sub_capmx subsetmx_refl (subsetmx_trans (subsetmx1 A)).
Qed.

Lemma capTmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  row_full A -> (A :&: B :=: B)%MS.
Proof.
by move=> m1 m2 n A B Afull; apply/eqmxP; rewrite capmxC !capmxT ?andbb.
Qed.

Let capmx_nop_id : forall n (A : 'M_n), capmx_nop A = A.
Proof. by move=> n A; rewrite /capmx_nop conform_mx_id. Qed.

Lemma cap1mx : forall n (A : 'M_n), (1%:M :&: A = A)%MS.
Proof. by move=> n A; rewrite mxopE capmx_id_eq1 eqxx capmx_nop_id. Qed.

Lemma capmx1 : forall n (A : 'M_n), (A :&: 1%:M = A)%MS.
Proof. by move=> n A; rewrite capmxC cap1mx. Qed.

Lemma capmxA : forall m1 m2 m3 n,
               forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A :&: (B :&: C) = A :&: B :&: C)%MS.
Proof.
move=> m1 m2 m3 n A B C; rewrite (capmxC A B) capmxC.
wlog idA: m1 m3 A C / (capmx_id A).
  move=> IH; case idA: (capmx_id A); first exact: IH.
  case idC: (capmx_id C); first by rewrite -IH.
  rewrite (@capmx_eq_norm n m3) ?capmx_id_cap ?idA ?idC ?andbF //.
  rewrite capmx_eq_norm ?capmx_id_cap ?idA ?idC ?andbF //.
  apply: capmx_norm_eq; first by rewrite !capmx_id_cap andbAC.
  by apply/andP; split; rewrite !sub_capmx andbAC -!sub_capmx.
rewrite -!(capmxC A) ![@capmx m1]mxopE idA capmx_nop_id.
case: (eqVneq (capmx_id B) (capmx_id C)) => [eqBC |].
  rewrite (@capmx_eq_norm n) ?capmx_nopP // capmx_eq_norm //.
  by apply: capmx_norm_eq; rewrite ?capmx_id_cap ?capmxS ?capmx_nopP.
by rewrite !mxopE capmx_nopP capmx_nop_id; do 2?case: capmx_id => //.
Qed.

Canonical Structure capmx_monoid n :=
  Monoid.Law (@capmxA n n n n) (@cap1mx n) (@capmx1 n).
Canonical Structure capmx_comoid n := Monoid.ComLaw (@capmxC n n n).

Lemma bigcapmx_inf : forall i0 P m n (A_ : I -> 'M_n) (B : 'M_(m, n)),
  P i0 -> (A_ i0 <= B -> \bigcap_(i | P i) A_ i <= B)%MS.
Proof.
move=> i0 P m n A_ B Pi0; apply: subsetmx_trans.
by rewrite (bigD1 i0) // capmxSl.
Qed.

Lemma sub_bigcapmxP : forall P m n (A : 'M_(m, n)) (B_ : I -> 'M_n),
  reflect (forall i, P i -> A <= B_ i)%MS (A <= \bigcap_(i | P i) B_ i)%MS.
Proof.
move=> P m n A B_; apply: (iffP idP) => [sAB i Pi | sAB].
  by apply: (subsetmx_trans sAB); rewrite (bigcapmx_inf Pi).
by apply big_prop => // [|B C sAC]; rewrite ?subsetmx1 // sub_capmx sAC.
Qed.

Lemma matrix_modl : forall m1 m2 m3 n,
                    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (A <= C -> A + (B :&: C) :=: (A + B) :&: C)%MS.
Proof.
move=> m1 m2 m3 n A B C sAC; set D := ((A + B) :&: C)%MS; apply/eqmxP.
rewrite sub_capmx sumsmxS ?capmxSl // sumsmx_sub sAC capmxSr /=.
have: (D <= B + A)%MS by rewrite sumsmxC capmxSl.
case/sub_sumsmxP=> A' sDA'B sA'A; rewrite -(addNKr A' D) subsetmx_add_sums //.
rewrite addrC sub_capmx sDA'B subsetmx_add ?capmxSr // eqmx_opp.
exact: subsetmx_trans sA'A sAC.
Qed.

Lemma matrix_modr : forall m1 m2 m3 n,
                    forall (A : 'M_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)),
  (C <= A -> (A :&: B) + C :=: A :&: (B + C))%MS.
Proof.
move=> m1 m2 m3 n A B C; rewrite !(capmxC A) -!(sumsmxC C); exact: matrix_modl.
Qed.

Lemma capmx_compl : forall m n (A : 'M_(m, n)), (A :&: A^C)%MS = 0.
Proof.
move=> m n A; set D := (A :&: A^C)%MS; have: (D <= D)%MS by [].
rewrite sub_capmx andbC; case/andP; case/subsetmxP=> B defB.
rewrite subsetmxE; move/eqP; rewrite defB -!mulmxA mulKVmx ?copid_mx_id //.
by rewrite mulmxA => ->; rewrite mul0mx.
Qed.

Lemma mxrank_mul_ker : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
  (\rank (A *m B) + \rank (A :&: kermx B))%N = \rank A.
Proof.
move=> m n p A B; apply/eqP; set K := kermx B; set C := (A :&: K)%MS.
rewrite -(eqmxMr B (eq_row_base A)); set K' := _ *m B.
rewrite -{2}(subnKC (rank_leq_row K')) -mxrank_ker eqn_addl.
rewrite -(mxrankMfree _ (row_base_free A)) mxrank_leqif_sup.
  rewrite sub_capmx -(eq_row_base A) subsetmxMl. 
  by apply/subsetmx_kerP; rewrite -mulmxA mulmx_ker.
have: (C <= row_base A)%MS by rewrite eq_row_base capmxSl.
case/subsetmxP=> C' defC; rewrite defC subsetmxMr //; apply/subsetmx_kerP.
by rewrite mulmxA -defC; apply/subsetmx_kerP; rewrite capmxSr.
Qed.

Lemma mxrank_disjoint_sum : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :&: B)%MS = 0  -> \rank (A + B)%MS = (\rank A + \rank B)%N.
Proof.
move=> m1 m2 n A B AB0; pose Ar := row_base A; pose Br := row_base B.
have [Afree Bfree]: row_free Ar /\ row_free Br by rewrite !row_base_free.
have: (Ar :&: Br <= A :&: B)%MS by rewrite capmxS ?eq_row_base.
rewrite {}AB0 subsetmx0 -mxrank_eq0 capmxE mxrankMfree //.
set Cr := col_mx Ar Br; set Crl := lsubmx _; rewrite mxrank_eq0 => Crl0.
rewrite -(sums_eqmx (eq_row_base _) (eq_row_base _)) sumsmxE -/Cr.
suffices K0: kermx Cr = 0.
  by apply/eqP; rewrite eqn_leq rank_leq_row -subn_eq0 -mxrank_ker K0 mxrank0.
move/eqP: (mulmx_ker Cr); rewrite -[kermx Cr]hsubmxK mul_row_col -/Crl.
rewrite (eqP Crl0) mul0mx add0r -mxrank_eq0 mxrankMfree // mxrank_eq0.
by move/eqP->; rewrite row_mx0.
Qed.

Lemma diffmxE : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B :=: A :&: (capmx_gen A B)^C)%MS.
Proof.
move=> m1 m2 n A B; rewrite mxopE; apply/eqmxP.
by rewrite !genmxE !capmxE andbb.
Qed.

Lemma diffmxSl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B <= A)%MS.
Proof. by move=> m1 m2 n A B; rewrite diffmxE capmxSl. Qed.

Lemma capmx_diff : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :\: B) :&: B)%MS = 0.
Proof.
move=> m1 m2 n A B; apply/eqP; pose C := capmx_gen A B.
rewrite -subsetmx0 -(capmx_compl C) sub_capmx -capmxE sub_capmx andbAC.
by rewrite -sub_capmx -diffmxE -sub_capmx.
Qed.

Lemma sumsmx_diff_cap_eq : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :\: B + A :&: B :=: A)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite sumsmx_sub capmxSl diffmxSl /=.
set C := (A :\: B)%MS; set D := capmx_gen A B.
suffices sACD: (A <= C + D)%MS.
  by rewrite (subsetmx_trans sACD) ?sumsmxS ?capmxE.
have:= sumsmx_compl_full D; rewrite /row_full sumsmxE.
case/row_fullP=> U; move/(congr1 (mulmx A)); rewrite mulmx1.
rewrite -[U]hsubmxK mul_row_col mulmx_addr addrC 2!mulmxA.
set V := _ *m _ => defA; rewrite -defA; move/(canRL (addrK _)): defA => defV.
have: (V <= C)%MS.
  rewrite diffmxE sub_capmx {1}defV -mulNmx subsetmx_add 1?subsetmxMtrans //.
  by rewrite -capmxE capmxSl.
by case/subsetmxP=> W ->; rewrite -mul_row_col sumsmxE subsetmxMl.
Qed.

Lemma mxrank_cap_compl : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (\rank (A :&: B) + \rank (A :\: B))%N = \rank A.
Proof.
move=> m1 m2 n A B; rewrite addnC -mxrank_disjoint_sum ?sumsmx_diff_cap_eq //.
by rewrite (capmxC A) capmxA capmx_diff cap0mx.
Qed.

Lemma mxrank_sum_cap : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (\rank (A + B) + \rank (A :&: B) = \rank A + \rank B)%N.
Proof.
move=> m1 m2 n A B; set C := (A :&: B)%MS; set D := (A :\: B)%MS.
have rDB: \rank (A + B)%MS = \rank (D + B)%MS.
  apply/eqP; rewrite mxrank_leqif_sup; first by rewrite sumsmxS ?diffmxSl.
  by rewrite sumsmx_sub sumsmxSr -(sumsmx_diff_cap_eq A B) sumsmxS ?capmxSr.
rewrite {1}rDB mxrank_disjoint_sum ?capmx_diff //.
by rewrite addnC addnA mxrank_cap_compl.
Qed.

Lemma mxrank_sums_leqif : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  \rank (A + B) <= \rank A + \rank B ?= iff (A :&: B <= (0 : 'M_n))%MS.
Proof.
move=> m1 m2 n A B; rewrite -mxrank_sum_cap; split; first exact: leq_addr.
by rewrite addnC (@eqn_addr _ 0) eq_sym mxrank_eq0 -subsetmx0.
Qed.

Section SumExpr.

(* This is the infrastructure to support the mxdirect predicate. We use a     *)
(* bespoke canonical structure to decompose a matrix expression into binary   *)
(* and n-ary products, using some of the "quote" technology. This lets us     *)
(* characterize direct sums as set sums whose rank is equal to the sum of the *)
(* ranks of the individual terms. The mxsum_expr/proper_mxsum_expr structures *)
(* below supply both the decomposition and the calculation of the rank sum.   *)
(* The mxsum_spec dependent predicate family expresses the consistency of     *)
(* these two decompositions.                                                  *)
(*   The main technical difficulty we need to overcome is the fact that       *)
(* the "catch-all" case of canonical structures has a priority lower than     *)
(* constant expansion. However, it is undesireable that local abbreviations   *)
(* be opaque for the direct-sum predicate, e.g., not be able to handle        *)
(* let S := (\sum_(i | P i) LargeExpression i)%MS in mxdirect S -> ...).      *)
(*   As in "quote", we use the interleaving of constant expansion and         *)
(* canonical projection matching to achieve our goal: we use a "wrapper" type *)
(* (indeed, the wrapped T type defined in ssrfun.v) with a self-inserting     *)
(* non-primitive constructor to gain finer control over the type and          *)
(* structure inference process. The innermost, primitive, constructor flags   *)
(* trivial sums; it is initially hidden by an eta-expansion, which has been   *)
(* made into a (default) canonical structure -- this lets type inference      *)
(* automatically insert this outer tag.                                       *)
(*   In detail, we define three types                                         *)
(*  mxsum_spec S r <-> There exists a finite list of matrices A1, ..., Ak     *)
(*                     such that S is the set sum of the Ai, and r is the sum *)
(*                     of the ranks of the Ai, i.e., S = (A1 + ... + Ak)%MS   *)
(*                     and r = \rank A1 + ... + \rank Ak. Note that           *)
(*                     mxsum_spec is a recursive dependent predicate family   *)
(*                     whose elimination rewrites simultaneaously S, r and    *)
(*                     the height of S.                                       *)
(*   proper_mxsum_expr n == The interface for proper sum expressions; this is *)
(*                     a double-entry interface, keyed on both the matrix sum *)
(*                     value and the rank sum. The matrix value is restricted *)
(*                     to square matrices, as the "+"%MS operator always      *)
(*                     returns a square matrix. This interface has two        *)
(*                     canonical insances, for binary and n-ary sums.         *)
(*   mxsum_expr m n == The interface for general sum expressions, comprising  *)
(*                     both proper sums and trivial sums consisting of a      *)
(*                     single matrix. The key values are WRAPPED as this lets *)
(*                     us give priority to the "proper sum" interpretation    *)
(*                     (see below). To allow for trivial sums, the matrix key *)
(*                     can have any dimension. The mxsum_expr interface has   *)
(*                     two canonical instances, for trivial and proper sums,  *)
(*                     keyed to the Wrap and wrap constructors, respectively. *)
(* The projections for the two interfaces above are                           *)
(*   proper_mxsum_val, mxsum_val : these are respectively coercions to 'M_n   *)
(*                     and wrapped 'M_(m, n); thus, the matrix sum for an     *)
(*                     S : mxsum_expr m n can be written unwrap S.            *)
(*   proper_mxsum_rank, mxsum_rank : projections to the nat and wrapped nat,  *)
(*                     respectively; the rank sum for S : mxsum_expr m n is   *)
(*                     thus written unwrap (mxsum_rank S).                    *)
(* The mxdirect A predicate actually gets A in a phantom argument, which is   *)
(* used to infer an (implicit) S : mxsum_expr such that unwrap S = A; the     *)
(* actual definition is \rank (unwrap S) == unwrap (mxsum_rank S).            *)
(*   Note that the inference of S is inherently ambiguous: ANY matrix can be  *)
(* viewed as a trivial sum, including one whose description is manifestly a   *)
(* proper sum. We use the wrapped type and the interaction between delta      *)
(* reduction and canonical structure inference to resolve this ambiguity in   *)
(* favor of proper sums, as follows:                                          *)
(*    - The phantom type sets up a unification problem of the form            *)
(*         unwrap (mxsum_val ?S) = A                                          *)
(*      with unknown evar ?S : mxsum_expr m n.                                *)
(*    - As the constructor wrap is also a default Canonical Structure for the *)
(*      wrapped type, so A is immediately replaced with unwrap (wrap A) and   *)
(*      we get the residual unification problem                               *)
(*         mxsum_val ?S = wrap A                                              *)
(*    - Now Coq tries to apply the proper sum Canonical Structure, which has  *)
(*      key projection wrap (proper_mxsum_val ?PS) where ?PS is a fresh evar  *)
(*      (of type proper_mxsum_expr n). This can only succeed if m = n, and if *)
(*      a solution can be found to the recursive unification problem          *)
(*         proper_mxsum_val ?PS = A                                           *)
(*      This causes Coq to look for one of the two canonical constants for    *)
(*      proper_mxsum_val (sumsmx or bigop) at the head of A, delta-expanding  *)
(*      A as needed, and then inferring recursively mxsum_expr structures for *)
(*      the last argument(s) of that constant.                                *)
(*    - If the above step fails then the wrap constant is expanded, revealing *)
(*      the primitive Wrap constructor; the unification problem now becomes   *)
(*         mxsum_val ?S = Wrap A                                              *)
(*      which fits perfectly the trivial sum canonical structure, whose key   *)
(*      projection is Wrap ?B where ?B is a fresh evar. Thus the inference    *)
(*      succeeds, and returns the trivial sum.                                *)
(* Note that the rank projections also register canonical values, so that the *)
(* same process can be used to infer a sum structure from the rank sum. In    *)
(* that case, however, there is no ambiguity and the inference can fail,      *)
(* because the rank sum for a trivial sum is not an arbitrary integer -- it   *)
(* must be of the form \rank ?B. It is nevertheless necessary to use the      *)
(* wrapped nat type for the rank sums, because in the non-trivial case the    *)
(* head constant of the nat expression is determined by the proper_mxsum_expr *)
(* canonical structure, so the mxsum_expr structure must use a generic        *)
(* constant, namely wrap.                                                     *)

Inductive mxsum_spec n : forall m, 'M[F]_(m, n) -> nat -> Prop :=
 | TrivialMxsum m A
    : @mxsum_spec n m A (\rank A)
 | ProperMxsum m1 m2 T1 T2 r1 r2 of
      @mxsum_spec n m1 T1 r1 & @mxsum_spec n m2 T2 r2
    : mxsum_spec (T1 + T2)%MS (r1 + r2)%N.
Arguments Scope mxsum_spec [nat_scope nat_scope matrix_set_scope nat_scope].

Structure mxsum_expr m n := Mxsum {
  mxsum_val :> wrapped 'M_(m, n);
  mxsum_rank : wrapped nat;
  _ : mxsum_spec (unwrap mxsum_val) (unwrap mxsum_rank)
}.

Canonical Structure trivial_mxsum m n A :=
  @Mxsum m n (Wrap A) (Wrap (\rank A)) (TrivialMxsum A).

Structure proper_mxsum_expr n := ProperMxsumExpr {
  proper_mxsum_val :> 'M_n;
  proper_mxsum_rank : nat;
  _ : mxsum_spec proper_mxsum_val proper_mxsum_rank
}.

Definition proper_mxsumP n (S : proper_mxsum_expr n) :=
  let: ProperMxsumExpr _ _ termS := S return mxsum_spec S (proper_mxsum_rank S)
  in termS.

Canonical Structure sum_mxsum n (S : proper_mxsum_expr n) :=
  @Mxsum n n (wrap (S : 'M_n)) (wrap (proper_mxsum_rank S)) (proper_mxsumP S).

Section Binary.
Variable (m1 m2 n : nat) (S1 : mxsum_expr m1 n) (S2 : mxsum_expr m2 n).
Fact binary_mxsum_proof :
  mxsum_spec (unwrap S1 + unwrap S2)
             (unwrap (mxsum_rank S1) + unwrap (mxsum_rank S2)).
Proof. by case: S1 S2 => [A1 r1 A1P] [A2 r2 A2P]; right. Qed.
Canonical Structure binary_mxsum_expr := ProperMxsumExpr binary_mxsum_proof.
End Binary.

Section Nary.
Variables (P : pred I) (n : nat) (S_ : I -> mxsum_expr n n).
Fact nary_mxsum_proof :
  mxsum_spec (\sum_(i | P i) unwrap (S_ i))
             (\sum_(i | P i) unwrap (mxsum_rank (S_ i))).
Proof.
rewrite -!(big_filter _ P) !unlock.
elim: filter => /= [|i e IHe]; first by rewrite -(mxrank0 n n); left.
by right=> //; case: (S_ i) => A r; exact.
Qed.
Canonical Structure nary_mxsum_expr := ProperMxsumExpr nary_mxsum_proof.
End Nary.

Definition mxdirect_def m n T of phantom 'M_(m, n) (unwrap (mxsum_val T)) :=
  \rank (unwrap T) == unwrap (mxsum_rank T).

End SumExpr.

Notation mxdirect A := (mxdirect_def (Phantom 'M_(_,_) A%MS)).

Lemma mxdirectP : forall n (S : proper_mxsum_expr n),
  reflect (\rank S = proper_mxsum_rank S) (mxdirect S).
Proof. move=> n S; exact: eqnP. Qed.
Implicit Arguments mxdirectP [n S].

Lemma mxdirect_trivial : forall m n A,
  mxdirect (unwrap (@trivial_mxsum m n A)).
Proof. move=> m n A; exact: eqxx. Qed.

Lemma mxrank_sum_leqif : forall m n (S : mxsum_expr m n),
  \rank (unwrap S) <= unwrap (mxsum_rank S) ?= iff mxdirect (unwrap S).
Proof.
rewrite /mxdirect_def => m n [[A] [r] /= defAr]; split=> //=.
elim: m A r / defAr => // m1 m2 A1 A2 r1 r2 _ leAr1 _ leAr2.
by apply: leq_trans (leq_add leAr1 leAr2); rewrite mxrank_sums_leqif.
Qed.

Lemma mxdirectE : forall m n (S : mxsum_expr m n),
  mxdirect (unwrap S) = (\rank (unwrap S) == unwrap (mxsum_rank S)).
Proof. by []. Qed.

Lemma mxdirectEgeq : forall m n (S : mxsum_expr m n),
  mxdirect (unwrap S) = (\rank (unwrap S) >= unwrap (mxsum_rank S)).
Proof.
by move=> m n S; rewrite leq_eqVlt ltnNge eq_sym !mxrank_sum_leqif orbF.
Qed.

Section BinaryDirect.

Variables m1 m2 n : nat.

Lemma mxdirect_sumsE : forall (S1 : mxsum_expr m1 n) (S2 : mxsum_expr m2 n),
   mxdirect (unwrap S1 + unwrap S2)
    = [&& mxdirect (unwrap S1), mxdirect (unwrap S2)
        & unwrap S1 :&: unwrap S2 == 0]%MS.
Proof.
move=> S1 S2; rewrite (@mxdirectE n) /=.
have:= leqif_add (mxrank_sum_leqif S1) (mxrank_sum_leqif S2).
move/(leqif_trans (mxrank_sums_leqif (unwrap S1) (unwrap S2)))=> ->.
by rewrite andbC -andbA subsetmx0.
Qed.

Lemma mxdirect_sumsP : forall (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :&: B = 0)%MS (mxdirect (A + B)).
Proof. move=> A B; rewrite mxdirect_sumsE !mxdirect_trivial; exact: eqP. Qed.

End BinaryDirect.

Section NaryDirect.

Variables (P : pred I) (n : nat).

Let TIsum A_ i := (A_ i :&: (\sum_(j | P j && (j != i)) A_ j) = 0 :> 'M_n)%MS.

Let mxdirect_bigsums_recP : forall S_ : I -> mxsum_expr n n,
  reflect (forall i, P i -> mxdirect (unwrap (S_ i)) /\ TIsum (unwrap \o S_) i)
          (mxdirect (\sum_(i | P i) (unwrap (S_ i)))).
Proof.
rewrite /TIsum => S_; apply: (iffP eqnP) => /= [dxS i Pi | dxS].
  set Si' := (\sum_(j | _) unwrap (S_ j))%MS.
  suffices: mxdirect (unwrap (S_ i) + Si').
    by rewrite mxdirect_sumsE; case/and3P=> -> _; move/eqP.
  by apply/eqnP; rewrite /= -!(bigD1 i).
elim: _.+1 {-2 4}P (subxx P) (ltnSn #|P|) => // m IHm Q; move/subsetP=> sQP.
case: (pickP Q) => [i Qi | Q0]; last by rewrite !big_pred0 ?mxrank0.
rewrite (cardD1x Qi) !((bigD1 i) Q) //=.
move/IHm=> <- {IHm}/=; last by apply/subsetP=> j; case/andP; move/sQP.
case: (dxS i (sQP i Qi)); move/eqnP=> <- TiQ_0; rewrite mxrank_disjoint_sum //.
apply/eqP; rewrite -subsetmx0 -{2}TiQ_0 capmxS //=; apply/bigsumsmx_subP=> j /=.
by case/andP=> Qj i'j; rewrite (bigsumsmx_sup j) ?[P j]sQP.
Qed.

Lemma mxdirect_bigsumsP : forall A_ : I -> 'M_n,
  reflect (forall i, P i -> A_ i :&: (\sum_(j | P j && (j != i)) A_ j) = 0)%MS
          (mxdirect (\sum_(i | P i) A_ i)).
Proof.
move=> A_; apply: (iffP (mxdirect_bigsums_recP _)) => dxA i; case/dxA=> //.
by rewrite mxdirect_trivial.
Qed.

Lemma mxdirect_bigsumsE : forall (S_ : I -> mxsum_expr n n) (xunwrap := unwrap),
  reflect (and (forall i, P i -> mxdirect (unwrap (S_ i)))
               (mxdirect (\sum_(i | P i) (xunwrap (S_ i)))))
          (mxdirect (\sum_(i | P i) (unwrap (S_ i)))).
Proof.
move=> S_; apply: (iffP (mxdirect_bigsums_recP _)) => [dxS | [dxS_ dxS] i Pi].
  by do [split; last apply/mxdirect_bigsumsP] => i; case/dxS.
by split; [exact: dxS_ | exact: mxdirect_bigsumsP Pi].
Qed.

End NaryDirect.

Section SubDsumsmx.

Variables m m1 m2 n : nat.
Variables (A : 'M[F]_(m, n)) (B1 : 'M[F]_(m1, n)) (B2 : 'M[F]_(m2, n)).

CoInductive sub_dsumsmx_spec : Prop :=
  SubDsumsmxSpec A1 A2 of (A1 <= B1)%MS & (A2 <= B2)%MS & A = A1 + A2
                        & forall C1 C2, (C1 <= B1)%MS -> (C2 <= B2)%MS ->
                          A = C1 + C2 -> C1 = A1 /\ C2 = A2.

Lemma sub_dsumsmx : (B1 :&: B2 = 0)%MS -> (A <= B1 + B2)%MS -> sub_dsumsmx_spec.
Proof.
move=> dxB; case/sub_sumsmxP=> A2 sAB1 sAB2.
exists (A - A2) A2; rewrite ?subrK // => C1 C2 sCB1 sCB2 defA.
suff: (C2 - A2 <= B1 :&: B2)%MS.
  by rewrite dxB subsetmx0 subr_eq0 defA; move/eqP->; rewrite addrK.
rewrite sub_capmx -{1}(canLR (addKr _) defA) -addrA.
by rewrite andbC 2?subsetmx_add ?eqmx_opp.
Qed.

End SubDsumsmx.

Section SubDbigsumsmx.

Variables (P : pred I) (m n : nat) (A : 'M[F]_(m, n)) (B : I -> 'M[F]_n).

CoInductive sub_bigdsumsmx_spec : Prop :=
  SubDbigsumsmxSpec A_ of forall i, P i -> (A_ i <= B i)%MS
                        & A = \sum_(i | P i) A_ i
                        & forall C, (forall i, P i -> C i <= B i)%MS ->
                          A = \sum_(i | P i) C i -> {in SimplPred P, C =1 A_}.

Lemma sub_bigdsumsmx :
    mxdirect (\sum_(i | P i) B i) -> (A <= \sum_(i | P i) B i)%MS ->
  sub_bigdsumsmx_spec.
Proof.
move/mxdirect_bigsumsP=> dxB; case/sub_bigsumsmxP=> u defA.
pose A_ i := u i *m B i.
exists A_ => //= [i _ | C sCB defAC i Pi]; first exact: subsetmxMl.
apply/eqP; rewrite -subr_eq0 -subsetmx0 -{dxB}(dxB i Pi) /=.
rewrite sub_capmx subsetmx_add ?eqmx_opp ?subsetmxMl ?sCB //=.
rewrite -(subrK A (C i)) -addrA -oppr_sub subsetmx_add ?eqmx_opp //.
  rewrite addrC defAC (bigD1 i) // addKr /= subsetmx_sum // => j Pi'j.
  by rewrite (bigsumsmx_sup j) ?sCB //; case/andP: Pi'j.
rewrite addrC defA (bigD1 i) // addKr /= subsetmx_sum // => j Pi'j.
by rewrite (bigsumsmx_sup j) ?subsetmxMl.
Qed.

End SubDbigsumsmx.

End RowSpaceTheory.

Hint Resolve subsetmx_refl.
Implicit Arguments subsetmxP [F m1 m2 n A B].
Implicit Arguments eq_row_sub [F m n v A].
Implicit Arguments row_subP [F m1 m2 n A B].
Implicit Arguments row_subPn [F m1 m2 n A B].
Implicit Arguments sub_rVP [F n u v].
Implicit Arguments rowV0Pn [F m n A].
Implicit Arguments rowV0P [F m n A].
Implicit Arguments row_fullP [F m n A].
Implicit Arguments row_freeP [F m n A].
Implicit Arguments eqmxP [F m1 m2 n A B].
Implicit Arguments genmxP [F m1 m2 n A B].
Implicit Arguments sub_sumsmxP [F m1 m2 m3 n A B C].
Implicit Arguments bigsumsmx_sup [F I P m n A B_].
Implicit Arguments bigsumsmx_subP [F I P m n A_ B].
Implicit Arguments sub_bigsumsmxP [F I P m n A B_].
Implicit Arguments subsetmx_kerP [F p m n A B].
Implicit Arguments det0P [F n A].
Implicit Arguments bigcapmx_inf [F I P m n A_ B].
Implicit Arguments sub_bigcapmxP [F I P m n A B_].
Implicit Arguments mxdirectP [F n S].
Implicit Arguments mxdirect_sumsP [F m1 m2 n A B].
Implicit Arguments mxdirect_bigsumsP [F I P n A_].
Implicit Arguments mxdirect_bigsumsE [F I P n S_].

Arguments Scope mxrank [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope complmx [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope row_full [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope subsetmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope eqmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope sumsmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope capmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope diffmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits mxrank genmx complmx subsetmx sumsmx capmx.
Notation "\rank A" := (mxrank A) : nat_scope.
Notation "<< A >>" := (genmx A) : matrix_set_scope.
Notation "A ^C" := (complmx A) : matrix_set_scope.
Notation "A <= B" := (subsetmx A B) : matrix_set_scope.
Notation "A <= B <= C" := ((subsetmx A B) && (subsetmx B C)) : matrix_set_scope.
Notation "A == B" := ((subsetmx A B) && (subsetmx B A)) : matrix_set_scope.
Notation "A :=: B" := (eqmx A B) : matrix_set_scope.
Notation "A + B" := (sumsmx A B) : matrix_set_scope.
Notation "A :&: B" := (capmx A B) : matrix_set_scope.
Notation "A :\: B" := (diffmx A B) : matrix_set_scope.
Notation mxdirect S := (mxdirect_def (Phantom 'M_(_,_) S%MS)).

Notation "\sum_ ( <- r | P ) B" :=
  (\big[sumsmx/0%R]_(<- r | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i <- r | P ) B" :=
  (\big[sumsmx/0%R]_(i <- r | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i <- r ) B" :=
  (\big[sumsmx/0%R]_(i <- r) B%MS) : matrix_set_scope.
Notation "\sum_ ( m <= i < n | P ) B" :=
  (\big[sumsmx/0%R]_(m <= i < n | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( m <= i < n ) B" :=
  (\big[sumsmx/0%R]_(m <= i < n) B%MS) : matrix_set_scope.
Notation "\sum_ ( i | P ) B" :=
  (\big[sumsmx/0%R]_(i | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ i B" :=
  (\big[sumsmx/0%R]_i B%MS) : matrix_set_scope.
Notation "\sum_ ( i : t | P ) B" :=
  (\big[sumsmx/0%R]_(i : t | P%B) B%MS) (only parsing) : matrix_set_scope.
Notation "\sum_ ( i : t ) B" :=
  (\big[sumsmx/0%R]_(i : t) B%MS) (only parsing) : matrix_set_scope.
Notation "\sum_ ( i < n | P ) B" :=
  (\big[sumsmx/0%R]_(i < n | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i < n ) B" :=
  (\big[sumsmx/0%R]_(i < n) B%MS) : matrix_set_scope.
Notation "\sum_ ( i \in A | P ) B" :=
  (\big[sumsmx/0%R]_(i \in A | P%B) B%MS) : matrix_set_scope.
Notation "\sum_ ( i \in A ) B" :=
  (\big[sumsmx/0%R]_(i \in A) B%MS) : matrix_set_scope.

Notation "\bigcap_ ( <- r | P ) B" :=
  (\big[capmx/1%:M]_(<- r | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i <- r | P ) B" :=
  (\big[capmx/1%:M]_(i <- r | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i <- r ) B" :=
  (\big[capmx/1%:M]_(i <- r) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( m <= i < n | P ) B" :=
  (\big[capmx/1%:M]_(m <= i < n | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( m <= i < n ) B" :=
  (\big[capmx/1%:M]_(m <= i < n) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i | P ) B" :=
  (\big[capmx/1%:M]_(i | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ i B" :=
  (\big[capmx/1%:M]_i B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i : t | P ) B" :=
  (\big[capmx/1%:M]_(i : t | P%B) B%MS) (only parsing) : matrix_set_scope.
Notation "\bigcap_ ( i : t ) B" :=
  (\big[capmx/1%:M]_(i : t) B%MS) (only parsing) : matrix_set_scope.
Notation "\bigcap_ ( i < n | P ) B" :=
  (\big[capmx/1%:M]_(i < n | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i < n ) B" :=
  (\big[capmx/1%:M]_(i < n) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i \in A | P ) B" :=
  (\big[capmx/1%:M]_(i \in A | P%B) B%MS) : matrix_set_scope.
Notation "\bigcap_ ( i \in A ) B" :=
  (\big[capmx/1%:M]_(i \in A) B%MS) : matrix_set_scope.

Section CardGL.

Variable F : finFieldType.

Lemma card_GL : forall n, n > 0 ->
  #|'GL_n[F]| = (#|F| ^ bin n 2 * \prod_(1 <= i < n.+1) (#|F| ^ i - 1))%N.
Proof.
case=> // n' _; set n := n'.+1; set p := #|F|.
rewrite big_nat_rev big_add1 -triangular_sum expn_sum -big_split /=.
pose fr m := [pred A : 'M[F]_(m, n) | \rank A == m].
set m := {-7}n; transitivity #|fr m|.
  by rewrite cardsT /= card_sub; apply: eq_card => A; rewrite -row_free_unit.
elim: m (leqnn m : m <= n) => [_|m IHm]; last move/ltnW=> le_mn.
  rewrite (@eq_card1 _ (0 : 'M_(0, n))) ?big_geq //= => A.
  by rewrite [A]flatmx0 !inE !eqxx.
rewrite big_nat_recr -{}IHm //= !subSS muln_subr muln1 -expn_add subnKC //.
rewrite -sum_nat_const /= -sum1_card -add1n.
rewrite (partition_big dsubmx (fr m)) /= => [|A]; last first.
  rewrite !inE -{1}(vsubmxK A); move: {A}(_ A) (_ A) => Ad Au Afull.
  rewrite eqn_leq rank_leq_row -(leq_add2l (\rank Au)) -mxrank_sum_cap.
  rewrite {1 3}[@mxrank]lock sumsmxE (eqnP Afull) -lock -addnA.
  by rewrite leq_add ?rank_leq_row ?leq_addr.
apply: eq_bigr => A rAm; rewrite (reindex (col_mx^~ A)) /=; last first.
  exists usubmx => [v _ | vA]; first by rewrite col_mxKu.
  by case/andP=> _; move/eqP <-; rewrite vsubmxK.
transitivity #|~: [set v *m A | v <- 'rV_m]|; last first.
  rewrite cardsCs setCK card_imset ?card_matrix ?card_ord ?mul1n //.
  have [B AB1] := row_freeP rAm; apply: can_inj (mulmx^~ B) _ => v.
  by rewrite -mulmxA AB1 mulmx1.
rewrite -sum1_card; apply: eq_bigl => v; rewrite !inE col_mxKd eqxx.
rewrite andbT eqn_leq rank_leq_row /= -(leq_add2r (\rank (v :&: A)%MS)).
rewrite -sumsmxE mxrank_sum_cap (eqnP rAm) addnAC leq_add2r ltn_neqAle andbC.
rewrite !mxrank_leqif_sup ?capmxSl // sub_capmx subsetmx_refl /=.
by congr (~~ _); apply/subsetmxP/imsetP=> [] [u]; exists u.
Qed.

(* An alternate, somewhat more elementary proof, that does not rely on the *)
(* row-space theory, but directly performs the LUP decomposition.          *)
Lemma LUP_card_GL : forall n, n > 0 ->
  #|'GL_n[F]| = (#|F| ^ bin n 2 * \prod_(1 <= i < n.+1) (#|F| ^ i - 1))%N.
Proof.
case=> // n' _; set n := n'.+1; set p := #|F|.
rewrite cardsT /= card_sub /GRing.unit /= big_add1 /= -triangular_sum -/n.
elim: {n'}n => [|n IHn].
  rewrite !big_geq // mul1n (@eq_card _ _ predT) ?card_matrix //= => M.
  by rewrite {1}[M]flatmx0 -(flatmx0 1%:M) unitmx1.
rewrite !big_nat_recr /= expn_add mulnAC mulnA -{}IHn -mulnA mulnC.
set LHS := #|_|; rewrite -[n.+1]muln1 -{2}[n]mul1n {}/LHS.
rewrite -!card_matrix subn1 -(cardC1 0) -mulnA; set nzC := predC1 _.
rewrite -sum1_card (partition_big lsubmx nzC) => [|A]; last first.
  rewrite unitmxE unitfE; apply: contra; move/eqP=> v0.
  rewrite -[A]hsubmxK v0 -[n.+1]/(1 + n)%N -col_mx0.
  rewrite -[rsubmx _]vsubmxK -det_tr tr_row_mx !tr_col_mx !trmx0.
  by rewrite det_lblock [0]mx11_scalar det_scalar1 mxE mul0r.
rewrite -sum_nat_const; apply: eq_bigr; rewrite /= -[n.+1]/(1 + n)%N => v nzv.
case: (pickP (fun i => v i 0 != 0)) => [k nza | v0]; last first.
  by case/eqP: nzv; apply/colP=> i; move/eqP: (v0 i); rewrite mxE.
have xrkK: involutive (@xrow F _ _ 0 k).
  by move=> m A /=; rewrite /xrow -row_permM tperm2 row_perm1.
rewrite (reindex_inj (inv_inj (xrkK (1 + n)%N))) /= -[n.+1]/(1 + n)%N.
rewrite (partition_big ursubmx xpredT) //= -sum_nat_const.
apply: eq_bigr => u _; set a : F := v _ _ in nza.
set v1 : 'cV_(1 + n) := xrow 0 k v.
have def_a: usubmx v1 = a%:M.
  by rewrite [_ v1]mx11_scalar mxE lshift0 mxE tpermL.
pose Schur := dsubmx v1 *m (a^-1 *m: u).
pose L : 'M_(1 + n) := block_mx a%:M 0 (dsubmx v1) 1%:M.
pose U B : 'M_(1 + n) := block_mx 1 (a^-1 *m: u) 0 B.
rewrite (reindex (fun B => L *m U B)); last first.
  exists (fun A1 => drsubmx A1 - Schur) => [B _ | A1].
    by rewrite mulmx_block block_mxKdr mul1mx addrC addKr.
  rewrite !inE mulmx_block !mulmx0 mul0mx !mulmx1 !addr0 mul1mx addrC subrK.
  rewrite mul_scalar_mx scalemxA divff // scale1mx andbC; case/and3P.
  move/eqP=> <- _; rewrite -{1}(hsubmxK A1) xrowE mul_mx_row row_mxKl -xrowE.
  move/eqP=> def_v; rewrite -def_a block_mxEh vsubmxK /v1 -def_v xrkK.
  apply: trmx_inj; rewrite tr_row_mx tr_col_mx trmx_ursub trmx_drsub trmx_lsub.
  by rewrite hsubmxK vsubmxK.
rewrite -sum1_card; apply: eq_bigl => B; rewrite xrowE unitmxE.
rewrite !det_mulmx unitr_mul -unitmxE unitmx_perm det_lblock det_ublock.
rewrite !det_scalar1 det1 mulr1 mul1r unitr_mul unitfE nza -unitmxE.
rewrite mulmx_block !mulmx0 mul0mx !addr0 !mulmx1 mul1mx block_mxKur.
rewrite mul_scalar_mx scalemxA divff // scale1mx eqxx andbT.
by rewrite block_mxEh mul_mx_row row_mxKl -def_a vsubmxK -xrowE xrkK eqxx andbT.
Qed.

Lemma card_GL_1 : #|'GL_1[F]| = #|F|.-1.
Proof. by rewrite card_GL // mul1n big_nat1 expn1 subn1. Qed.

Lemma card_GL_2 : #|'GL_2[F]| = (#|F| * #|F|.-1 ^ 2 * #|F|.+1)%N.
Proof.
rewrite card_GL // big_ltn // big_nat1 expn1 -(addn1 #|F|) -subn1 -!mulnA.
by rewrite -subn_sqr.
Qed.

End CardGL.

Lemma logn_card_GL_p : forall n p, prime p -> logn p #|'GL_n(p)| = bin n 2.
Proof.
move=> n p p_pr; have p_gt1 := prime_gt1 p_pr.
have p_i_gt0: p ^ _ > 0 by move=> i; rewrite expn_gt0 ltnW.
rewrite (card_GL _ (ltn0Sn n.-1)) card_ord Fp_cast // big_add1 /=.
pose p'gt0 m := m > 0 /\ logn p m = 0%N.
suffices [Pgt0 p'P]: p'gt0 (\prod_(0 <= i < n.-1.+1) (p ^ i.+1 - 1))%N.
  by rewrite logn_mul // p'P pfactorK //; case n.
apply big_prop => [|m1 m2 [m10 p'm1] [m20]|i _]; rewrite {}/p'gt0 ?logn1 //.
  by rewrite muln_gt0 m10 logn_mul ?p'm1.
rewrite lognE -if_neg subn_gt0 p_pr /= -{1 2}(exp1n i.+1) ltn_exp2r // p_gt1.
by rewrite dvdn_subr ?dvdn_exp // gtnNdvd.
Qed.

(* Parametricity at the field level (note that the unit/inverse are only     *)
(* mapped at this level).                                                    *)
Section MapFieldMatrix.

Variables (aF rF : fieldType) (f : aF -> rF).
Hypothesis fRM : GRing.morphism f.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma map_mx_inj : forall m n, injective ((map_mx f) m n).
Proof.
move=> m n A B; move/matrixP=> eq_AB; apply/matrixP=> i j.
by move/(_ i j): eq_AB; rewrite !mxE; exact: fieldM_inj.
Qed.

Lemma map_unitmx : forall n (A : 'M_n), (A^f \in unitmx) = (A \in unitmx).
Proof. by move=> n A; rewrite unitmxE det_map_mx // fieldM_unit // -unitfE. Qed.

Lemma map_mx_unit : forall n' (A : 'M_n'.+1), GRing.unit A^f = GRing.unit A.
Proof. by move=> n'; exact: map_unitmx. Qed.

Lemma map_invmx : forall n (A : 'M_n), (invmx A)^f = invmx A^f.
Proof.
move=> n A; rewrite /invmx map_unitmx (fun_if ((map_mx f) n n)).
by rewrite map_mxZ // map_mx_adj // det_map_mx // fieldM_inv. 
Qed.

Lemma map_mx_inv : forall n' (A : 'M_n'.+1), A^-1^f = A^f^-1.
Proof. by move=> n'; exact: map_invmx. Qed.

Lemma emxrank_map : forall m n (A : 'M_(m, n)),
  emxrank A^f = ((col_ebase A)^f, (row_ebase A)^f, \rank A).
Proof.
rewrite /row_ebase /col_ebase /mxrank.
elim=> [|m IHm] [|n] A /=; rewrite ?map_mx1 //.
set pAnz := fun k => A k.1 k.2 != 0.
rewrite (@eq_pick _ _ pAnz) => [|k]; last by rewrite mxE fieldM_eq0.
case: {+}(pick _) => [[i j]|]; last by rewrite !map_mx1.
rewrite mxE -fieldM_inv // -map_xcol -map_xrow -map_dlsubmx -map_drsubmx.
rewrite -map_ursubmx -map_mxZ // -map_mxM // -map_mx_sub // {}IHm /=.
case: {+}(emxrank _) => [[L U] r] /=; rewrite map_xrow map_xcol.
by rewrite !(@map_block_mx _ _ f 1 _ 1) !map_mx0 ?map_mx1 ?map_scalar_mx.
Qed.

Lemma mxrank_map : forall m n (A : 'M_(m, n)), \rank A^f = \rank A.
Proof. by move=> m n A; rewrite {1}/mxrank emxrank_map. Qed.

Lemma map_mx_eq0 : forall m n (A : 'M_(m, n)), (A^f == 0) = (A == 0).
Proof. by move=> m n A; rewrite -!mxrank_eq0 mxrank_map. Qed.

Lemma row_free_map : forall m n (A : 'M_(m, n)), row_free A^f = row_free A.
Proof. by move=> m n A; rewrite /row_free mxrank_map. Qed.

Lemma row_full_map : forall m n (A : 'M_(m, n)), row_full A^f = row_full A.
Proof. by move=> m n A; rewrite /row_full mxrank_map. Qed.

Lemma map_row_ebase : forall m n (A : 'M_(m, n)),
  (row_ebase A)^f = row_ebase A^f.
Proof. by move=> m n A; rewrite {2}/row_ebase emxrank_map. Qed.

Lemma map_col_ebase : forall m n (A : 'M_(m, n)),
  (col_ebase A)^f = col_ebase A^f.
Proof. by move=> m n A; rewrite {2}/col_ebase emxrank_map. Qed.

Lemma map_row_base : forall m n (A : 'M_(m, n)),
  (row_base A)^f = castmx (mxrank_map A, erefl n) (row_base A^f).
Proof.
move=> m n A; move: (mxrank_map A); rewrite {2}/row_base mxrank_map => eqrr.
by rewrite castmx_id map_mxM // map_pid_mx // map_row_ebase.
Qed.

Lemma map_col_base : forall m n (A : 'M_(m, n)),
  (col_base A)^f = castmx (erefl m, mxrank_map A) (col_base A^f).
Proof.
move=> m n A; move: (mxrank_map A); rewrite {2}/col_base mxrank_map => eqrr.
by rewrite castmx_id map_mxM // map_pid_mx // map_col_ebase.
Qed.

Lemma map_pinvmx : forall m n (A : 'M_(m, n)), (pinvmx A)^f = pinvmx A^f.
Proof.
move=> m n A; rewrite !map_mxM // !map_invmx map_row_ebase map_col_ebase.
by rewrite map_pid_mx // -mxrank_map.
Qed.

Lemma map_kermx : forall m n (A : 'M_(m, n)), (kermx A)^f = kermx A^f.
Proof.
move=> m n A; rewrite !map_mxM // map_invmx map_col_ebase -mxrank_map.
by rewrite map_copid_mx.
Qed.

Lemma map_cokermx : forall m n (A : 'M_(m, n)), (cokermx A)^f = cokermx A^f.
Proof.
move=> m n A; rewrite !map_mxM // map_invmx map_row_ebase -mxrank_map.
by rewrite map_copid_mx.
Qed.

Lemma subsetmx_map : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A^f <= B^f)%MS = (A <= B)%MS.
Proof.
by move=> m1 m2 n A B; rewrite !subsetmxE -map_cokermx -map_mxM // map_mx_eq0.
Qed.

Lemma eqmx_map : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A^f :=: B^f)%MS <-> (A :=: B)%MS.
Proof.
move=> m1 m2 n A B; split=> [|eqAB].
  by move/eqmxP; rewrite !subsetmx_map; move/eqmxP.
by apply/eqmxP; rewrite !subsetmx_map !eqAB !subsetmx_refl.
Qed.

Lemma map_genmx : forall m n (A : 'M_(m, n)), (<<A>>^f :=: <<A^f>>)%MS.
Proof.
by move=> m n A; apply/eqmxP; rewrite !(genmxE, subsetmx_map) andbb.
Qed.

Lemma map_sumsmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (((A + B)%MS)^f :=: A^f + B^f)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite !sumsmxE -map_col_mx !subsetmx_map.
by rewrite !sumsmxE andbb.
Qed.

Let map_capmx_gen : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (capmx_gen A B)^f = capmx_gen A^f B^f.
Proof.
by move=> m1 m2 n A B; rewrite map_mxM // map_lsubmx map_kermx map_col_mx.
Qed.

Lemma map_capmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :&: B)^f :=: A^f :&: B^f)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite !capmxE -map_capmx_gen.
by rewrite !subsetmx_map -!capmxE andbb.
Qed.

Lemma map_complmx : forall m n (A : 'M_(m, n)), (A^C^f = A^f^C)%MS.
Proof.
by move=> m n A; rewrite map_mxM // map_row_ebase -mxrank_map map_copid_mx.
Qed.

Lemma map_diffmx : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  ((A :\: B)^f :=: A^f :\: B^f)%MS.
Proof.
move=> m1 m2 n A B; apply/eqmxP; rewrite !diffmxE -map_capmx_gen -map_complmx.
by rewrite -!map_capmx !subsetmx_map -!diffmxE andbb.
Qed.

End MapFieldMatrix.