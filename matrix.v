(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype connect.
Require Import finfun ssralg bigops groups group_perm signperm.

(* Require Import div finset zp. *)

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50,
   format "\matrix_ ( i  <  m ,  j  <  n )  E").
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50,
   format "\matrix_ ( i ,  j  <  n )  E").

Reserved Notation "''M_' n"       (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").
Reserved Notation "''M_' ( n )"   (at level 8, only parsing).

Reserved Notation "\0_ n"         (at level 8, n at level 2, format "\0_ n").
Reserved Notation "\0_ ( m , n )" (at level 8, format "\0_ ( m ,  n )").
Reserved Notation "\0_ ( n )"     (at level 8, only parsing).
Reserved Notation "\0"            (at level 8, format "\0").
Reserved Notation "\1_ n"         (at level 8, n at level 2, format "\1_ n").
Reserved Notation "\1"            (at level 8, format "\1").
Reserved Notation "\Z_ n x"       (at level 10, n at level 2, x at level 8,
                                   format "\Z_ n  x").
Reserved Notation "\Z x"          (at level 10, x at level 8, format "\Z  x").
Reserved Notation "\P s"          (at level 10, s at level 8, format "\P  s").

Reserved Notation "A +m B"    (at level 50, format "A  +m  B").
Reserved Notation "x *s A"    (at level 40, format "x  *s  A").
Reserved Notation "A *m B"    (at level 40, format "A  *m  B").
Reserved Notation "\^t A"     (at level 10, A at level 8, format "\^t  A").
Reserved Notation "\tr A"     (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"    (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"    (at level 10, A at level 8, format "\adj  A").

Delimit Scope matrix_scope with MX.

Import Ring.
Notation Local simp := (Monoid.Equations.simpm, oppr0).

Open Scope ring_scope.
Open Scope matrix_scope.

Section MatrixDef.

Variable R : basic. (* commutative_. *)
Variables m n : nat.

(* Basic linear algebra (matrices).                                       *)
(*   We use dependent types (ordinals) for the indices so that ranges are *)
(* mostly inferred automatically; we may have to reconsider this design   *)
(* if it proves too unwieldly for block decomposition theory.             *)

CoInductive matrix : Type := Matrix of {ffun 'I_m * 'I_n -> R}.

Notation "''M_' ( m , n )" := (matrix m n).
Notation "''M_' ( n )" := 'M_(n, n).
Notation "''M_' n" := 'M_(n).

Definition matrix_val A := let: Matrix g := A in g.

Lemma can_matrix_val : cancel matrix_val Matrix. Proof. by case. Qed.

Canonical Structure matrix_eqType := CanEqType can_matrix_val.

Definition matrix_of_fun F := locked Matrix [ffun ij => F ij.1 ij.2].

Definition fun_of_matrix := locked (fun A i j => matrix_val A (i, j)).

Coercion fun_of_matrix  : matrix >-> Funclass.

Lemma mxK : forall F, matrix_of_fun F =2 F.
Proof. by unlock matrix_of_fun fun_of_matrix => F i j; rewrite /= ffunE. Qed.

Lemma matrixP : forall A B : matrix, A =2 B <-> A = B.
Proof.
unlock fun_of_matrix => [] [A] [B]; split=> [/= eqAB | -> //].
congr Matrix; apply/ffunP=> [] [i j]; exact: eqAB.
Qed.

End MatrixDef.

Open Scope matrix_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n (fun i j => E)) (only parsing) : matrix_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : matrix_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : matrix_scope.

(* Definition of operations for matrix over a ring *)
Section MatrixOpsDef.

Variable R : Ring.basic.

Notation Local "''M_' ( m , n )" := (matrix R m n) : type_scope.
Notation Local "''M_' ( n )" := 'M_(n, n) : type_scope.
Notation Local "''M_' n" := 'M_(n) : type_scope.

Definition addmx m n (A B : 'M_(m, n)) :=
  \matrix_(i, j) (A i j + B i j).

Definition scalemx m n x (A : 'M_(m, n)) := \matrix_(i, j) (x * A i j).

Definition mulmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i, k) \sum_j (A i j * B j k).

Definition null_mx m n : 'M_(m, n) := \matrix_(i, j) 0.

Definition scalar_mx n x : 'M_n :=
  \matrix_(i, j) (if i == j then x else 0).

Definition unit_mx n := scalar_mx n 1.

Definition mx_row m n i0 (A : 'M_(m, n)) := \matrix_(i < 1, j < n) A i0 j.

Definition mx_col m n j0 (A : 'M_(m, n)) := \matrix_(i < m, j < 1) A i j0.

Definition mx_rem_row m n i0 (A : 'M_(m, n)) :=
  \matrix_(i, j) A (lift i0 i) j.

Definition mx_rem_col m n j0 (A : 'M_(m, n)) :=
  \matrix_(i, j) A i (lift j0 j).

(* The shape of the (dependent) height parameter determines where *)
(* the cut is made! *)

Definition mx_lcut m1 m2 n (A : 'M_(m1 + m2, n)) :=
  \matrix_(i, j) A (lshift m2 i) j.

Definition mx_rcut m1 m2 n (A : 'M_(m1 + m2, n)) :=
  \matrix_(i, j) A (rshift m1 i) j.

Definition mx_paste m1 m2 n (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) :=
   \matrix_(i, j) match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.


Definition trmx m n (A : 'M_(m, n)) := \matrix_(i, j) A j i.

Definition perm_mx n (s : 'S_n) : 'M_n :=
   \matrix_(i, j) (if s i == j then 1 else 0).

(* The trace, in 1/4 line. *)
Definition mx_trace (n : nat) (A : 'M_n) := \sum_i (A i i).

(* The determinants, in one line. *)
Definition determinant n (A : 'M_n) :=
  \sum_(s : 'S_n) (-1)^+s * \prod_i A i (s i).

Notation Local "'\det' A" := (determinant A).
Notation Local row' := mx_rem_row.
Notation Local col' := mx_rem_col.

(* And now, the Laplace formula. *)

Definition cofactor n (A : 'M_n) (i j : 'I_n) :=
   (-1) ^+(i + j) * \det (row' i (col' j A)).


(* The final flurry: adjugates. *)

Definition adjugate n (A : 'M_n) := \matrix_(i, j) (cofactor A j i).

(* Operator syntax, basic style.                     *)
(* Generic syntax would really help here...          *)
(*
Notation "\0_ ( m , n )" := (null_mx m n) (only parsing) : matrix_scope.
Notation "\0_ ( n )" := \0_(n, n) (only parsing) : matrix_scope.
Notation "\0" := \0_(_, _) : matrix_scope.
Notation "\1_ ( n )" := (unit_mx n) (only parsing) : matrix_scope.
Notation "\1" := \1_(_) : matrix_scope.
Notation "\Z_ ( n ) x" := (scalar_mx n x) (only parsing) : matrix_scope.
Notation "\Z x" := (\Z_(_) x) : matrix_scope.
Notation "\P s" := (perm_mx s) : matrix_scope.
Notation "A +m B" := (addmx A B) : matrix_scope.
Notation "x *s A" := (scalemx x A) : matrix_scope.
Notation "A *m B" := (mulmx A B) : matrix_scope.
Notation "\^t A" := (trmx A) : matrix_scope.
*)
End MatrixOpsDef.

Notation "\0_ ( m , n )" := (null_mx _ m n) (only parsing) : matrix_scope.
Notation "\0_ ( n )" := \0_(n, n) (only parsing) : matrix_scope.
Notation "\0_ n" := \0_(n) (only parsing) : matrix_scope.
Notation "\0" := \0_(_, _) : matrix_scope.
Notation "\1_ n" := (unit_mx _ n) (only parsing) : matrix_scope.
Notation "\1" := \1_(_) : matrix_scope.
Notation "\Z_ n x" := (scalar_mx n x) (only parsing) : matrix_scope.
Notation "\Z x" := (\Z_(_) x) : matrix_scope.
Notation "\P s" := (perm_mx _ s) : matrix_scope.
Notation "A +m B" := (addmx A B) : matrix_scope.
Notation "x *s A" := (scalemx x A) : matrix_scope.
Notation "A *m B" := (mulmx A B) : matrix_scope.
Notation "\^t A" := (trmx A) : matrix_scope.

Notation "'\tr' A" := (mx_trace A) : ring_scope.
Notation "'\det' A" := (determinant A) : ring_scope.
Notation "'\adj' A" := (adjugate A) : ring_scope.

Section MatrixOnRingProp.
Variable R : Ring.basic.

Notation Local "''M_' ( m , n )" := (matrix R m n) : type_scope.
Notation Local "''M_' ( n )" := 'M_(n, n) : type_scope.
Notation Local "''M_' n" := 'M_(n) : type_scope.
Notation Local row := mx_row.
Notation Local row' := mx_rem_row.
Notation Local col := mx_col.
Notation Local col' := mx_rem_col.
Notation Local lcut := mx_lcut.
Notation Local rcut := mx_rcut.
Notation Local paste := mx_paste.

Lemma perm_mx1 : forall n, \P 1%g = \1 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxK perm1. Qed.

Lemma trmxK : forall m n, cancel (@trmx R m n) (@trmx R n m).
Proof. by move=> m n A; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma trmx_inj : forall m n, injective (@trmx R m n).
Proof. move=> m n; exact: can_inj (@trmxK m n). Qed.

Lemma trmx_perm : forall n (s : 'S_n), \^t (\P s) = \P (s^-1) :> 'M_n.
Proof.
by move=> n s; apply/matrixP=> i j; rewrite !mxK eq_sym (canF_eq (permKV s)).
Qed.

Lemma trmxZ : forall n x, \^t (\Z x) = \Z x :> 'M_n.
Proof. by move=> n x; apply/matrixP=> i j; rewrite !mxK eq_sym. Qed.

Lemma trmx1 : forall n, \^t \1 = \1 :> 'M_n.
Proof. move=> n; exact: trmxZ. Qed.

Lemma trmx0 : forall n, \^t \0 = \0 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma tr_addmx : forall m n (A B : 'M_(m, n)),
  \^t (A +m B) = \^t A +m \^t B.
Proof. by move=> m n A B; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma tr_scalemx : forall m n x (A : 'M_(m, n)),
  \^t (x *s A) = x *s \^t A.
Proof. by move=> m n x A; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma tr_row : forall m n i0 (A : 'M_(m, n)),
  \^t (row i0 A) = col i0 (\^t A).
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma tr_rem_row : forall m n i0 (A : 'M_(m, n)),
  \^t (row' i0 A) = col' i0 (\^t A).
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma tr_col : forall m n j0 (A : 'M_(m, n)),
  \^t (col j0 A) = row j0 (\^t A).
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma tr_rem_col : forall m n j0 (A : 'M_(m, n)),
  \^t (col' j0 A) = row' j0 (\^t A).
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxK. Qed.

Lemma mx_eq_row : forall m n i0 (A : 'M_(m, n)) B,
  row i0 A = B -> A i0 =1 B ord0.
Proof. move=> m n i0 A B [eqAB] j; by rewrite -eqAB !mxK. Qed.

Lemma mx_eq_rem_row : forall m n i i0 (A B : 'M_(m, n)),
  i0 != i -> row' i0 A = row' i0 B -> A i =1 B i.
Proof.
move=> m n i i0 A B; case/unlift_some=> i' -> _  [eqAB] j.
by move/matrixP: eqAB; move/(_ i' j); rewrite !mxK.
Qed.

Lemma mx_paste_cut : forall m1 m2 n (A : 'M_(m1 + m2, n)),
  paste (lcut A) (rcut A) = A.
Proof.
move=> m1 m2 n A; apply/matrixP=> i j; rewrite !mxK.
case: splitP => k Dk //=; rewrite !mxK //=; congr (A _ _); exact: val_inj.
Qed.

(* The matrix graded algebra. *)

Lemma add0mx : forall m n (A : 'M_(m, n)), \0 +m A = A.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK simp. Qed.

Lemma addmxC : forall m n (A B : 'M_(m, n)), A +m B = B +m A.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK addrC. Qed.

Lemma addmxA : forall m n (A B C : 'M_(m, n)),
  A +m (B +m C) = A +m B +m C.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK addrA. Qed.

Lemma scale0mx : forall m n (A : 'M_(m, n)), 0 *s A = \0.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK simp. Qed.

Lemma scalemx0 : forall m n c, c *s \0 = \0 :> 'M_(m, n).
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK simp. Qed.

Lemma scale1mx : forall m n (A : 'M_(m, n)), 1 *s A = A.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK simp. Qed.

Lemma scalarmx0 : forall n, \Z 0 = \0 :> 'M_n.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK if_same. Qed.

Lemma scalarmx1 : forall n, \Z 1 = \1 :> 'M_n.
Proof. done. Qed.

Lemma scalemxA : forall m n c1 c2 (A : 'M_(m, n)),
  c1 *s (c2 *s A) = (c1 * c2) *s A.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK mulrA. Qed.

Lemma scalemx1 : forall n c, c *s \1 = \Z c :> 'M_n.
Proof. by move=> *; apply/matrixP=> i j; rewrite 2!mxK fun_if !simp mxK. Qed.

Lemma scalemx_addl : forall m n x1 x2 (A : 'M_(m, n)),
  (x1 + x2) *s A = x1 *s A +m x2 *s A.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK mulr_addl. Qed.

Lemma scalemx_addr : forall m n x (A B : 'M_(m, n)),
  x *s (A +m B) = x *s A +m x *s B.
Proof. by move=> *; apply/matrixP=> i j; rewrite !mxK mulr_addr. Qed.

Lemma scalemxAl : forall m n p x (A : 'M_(m, n)) (B : 'M_(n, p)),
  x *s (A *m B) = (x *s A) *m B.
Proof.
move=> *; apply/matrixP=> i k; rewrite !mxK big_distrr /=.
by apply: eq_bigr => j _; rewrite mulrA mxK.
Qed.

Lemma addmxN : forall m n (A : 'M_(m, n)), A +m (-1 *s A) = \0.
Proof. by move=> m n A; apply/matrixP=> i j; rewrite !mxK mulN1r addrN. Qed.

Lemma addNmx : forall m n (A : 'M_(m, n)), (- 1 *s A) +m A = \0.
Proof. by move=> m n A; apply/matrixP=> i j; rewrite !mxK mulN1r addNr. Qed.

Lemma mul1mx : forall m n (A : 'M_(m, n)), \1 *m A = A.
Proof.
move=> m n A; apply/matrixP=> i j; rewrite !mxK (bigD1 i) //= mxK eqxx.
by rewrite big1 ?simp //= => k ne_ki; rewrite mxK eq_sym (negbET ne_ki) simp.
Qed.

Lemma mult0mx : forall m n p (A : 'M_(n, p)), \0 *m A = \0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k; rewrite !mxK big1 ?simp //= => j _.
by rewrite mxK simp.
Qed.

Lemma multmx0 : forall m n p (A : 'M_(m, n)), A *m \0 = \0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k; rewrite !mxK big1 ?simp //= => j _.
by rewrite mxK simp.
Qed.

Lemma mulmx1 : forall m n (A : 'M_(m, n)), A *m \1 = A.
Proof.
move=> m n A; apply/matrixP=> i k; rewrite !mxK.
rewrite (bigD1 k) //= !mxK eq_refl mulr1 -{-1}(addr0 (A i k)); congr (_ + _).
by apply: big1 => j Hj; rewrite mxK (negbET Hj) simp.
Qed.

Lemma mulmx_addl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 +m A2) *m B = A1 *m B +m A2 *m B.
Proof.
move=> m n p A1 A2 B; apply/matrixP=> i k; rewrite !mxK -big_split /=.
by apply: eq_bigr => j _; rewrite mxK mulr_addl.
Qed.

Lemma mulmx_addr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 +m B2) = A *m B1 +m A *m B2.
Proof.
move=> m n p A B1 B2; apply/matrixP=> i k; rewrite !mxK -big_split /=.
by apply: eq_bigr => j _; rewrite mxK mulr_addr.
Qed.

Lemma mulmxA : forall m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)),
  A *m (B *m C) = A *m B *m C.
Proof.
move=> m n p q A B C; apply/matrixP=> i l; rewrite !mxK.
transitivity (\sum_j (\sum_k (A i j * (B j k * C k l)))).
  by apply: eq_bigr => j _; rewrite mxK big_distrr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxK big_distrl /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

Canonical Structure matrix_additive_group m n :=
  AdditiveGroup (@addmxA m n) (@addmxC m n) (@add0mx m n) (@addNmx m n).

(* the additive group structure provides generic sums. *)

Lemma mxK_sum : forall m n I r (P : pred I) (F : I -> 'M_(m, n)) i j,
  (\sum_(k <- r | P k) F k) i j = \sum_(k <- r | P k) F k i j.
Proof.
move=> m n I r P F i j; apply: (big_morph (fun A : 'M_(m, n) => A i j)).
by split=> [|A B]; rewrite !mxK.
Qed.

(* To make a true matrix ring the order needs to be positive!       *)
(* We use a structure to encode that info; it is defined in ssrnat. *)

Section MatrixRing.

Variable n : pos_nat.

Lemma nonzeromx1 : \1 <> \0 :> 'M_n.
Proof.
rewrite -(ltn_predK (pos_natP n)); move/matrixP; move/(_ ord0 ord0).
rewrite !mxK; exact: nonzero1r.
Qed.

Canonical Structure matrix_ring : Ring.basic :=
  Basic (@mulmxA n n n n) (@mul1mx n n) (@mulmx1 n n)
        (@mulmx_addl n n n) (@mulmx_addr n n n) nonzeromx1.

End MatrixRing.

Lemma perm_mxM : forall n (s t : 'S_n), \P (s * t)%g = \P s *m \P t :> 'M_n.
Proof.
move=> n s t; apply/matrixP=> i j; rewrite !mxK (bigD1 (s i)) //= !mxK eqxx.
rewrite simp -permM big1 /= => [|k ne_k_si]; first by rewrite addrC simp.
by rewrite mxK /= eq_sym (negbET ne_k_si) simp.
Qed.

Lemma trace_addmx : forall n (A B : 'M_n), \tr (A +m B) = \tr A + \tr B.
Proof.
by move=> n A B; rewrite -big_split; apply: eq_bigr => i _; rewrite mxK.
Qed.

Lemma trace_scalemx : forall n x (A : 'M_n), \tr (x *s A) = x * \tr A.
Proof.
by move=> *; rewrite big_distrr; apply: eq_bigr => i _; rewrite mxK.
Qed.

Lemma trace_tr : forall n (A : 'M_n), \tr (\^t A) = \tr A.
Proof. by move => *;  apply: eq_bigr => i _; rewrite mxK. Qed.

End MatrixOnRingProp.

Section MatrixOnComRingProp.
Variable R : Ring.commutative_.

Notation Local "''M_' ( m , n )" := (matrix R m n) : type_scope.
Notation Local "''M_' ( n )" := 'M_(n, n) : type_scope.
Notation Local "''M_' n" := 'M_(n) : type_scope.
Notation Local row := mx_row.
Notation Local row' := mx_rem_row.
Notation Local col := mx_col.
Notation Local col' := mx_rem_col.
Notation Local lcut := mx_lcut.
Notation Local rcut := mx_rcut.
Notation Local paste := mx_paste.

Lemma scalemxAr : forall m n p x (A : 'M_(m, n)) (B : 'M_(n, p)),
  x *s (A *m B) = A *m (x *s B).
Proof.
move=> *; apply/matrixP=> i k; rewrite !mxK big_distrr /=.
by apply: eq_bigr => j _; rewrite mxK mulrCA.
Qed.

Lemma tr_mulmx : forall m n p (A : 'M_(m, n)) (B : 'M_(n, p)),
   \^t (A *m B) = \^t B *m \^t A.
Proof.
move=> *; apply/matrixP=> i k; rewrite !mxK; apply: eq_bigr => j _.
by rewrite !mxK mulrC.
Qed.

Lemma trace_mulmxC : forall m n (A : 'M_(m, n)) (B : 'M_(n, m)),
  \tr (A *m B) = \tr (B *m A).
Proof.
move=> m n A B; transitivity (\sum_i \sum_j A i j * B j i).
  by apply: eq_bigr => i _; rewrite mxK.
rewrite exchange_big; apply: eq_bigr => i _ /=; rewrite mxK.
apply: eq_bigr => j _; exact: mulrC.
Qed.

Lemma determinant_multilinear : forall n (A B C : 'M_n) i0 b c,
    row i0 A =2 b *s row i0 B +m c *s row i0 C ->
    row' i0 B =2 row' i0 A ->
    row' i0 C =2 row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c ABC; move/matrixP=> BA; move/matrixP=> CA.
move/mx_eq_rem_row: BA => BA; move/mx_eq_rem_row: CA => CA.
rewrite !big_distrr -big_split; apply: eq_bigr => s _ /=.
rewrite -!(mulrCA (_ ^+s)) -mulr_addr; congr (_ * _).
rewrite !(bigD1 i0 (_ : predT i0)) //=.
move/matrixP: ABC => ABC; rewrite (mx_eq_row ABC) !mxK mulr_addl !mulrA.
by congr (_ * _ + _ * _); apply: eq_bigr => i ?; rewrite ?BA ?CA // eq_sym.
Qed.

Lemma alternate_determinant : forall n (A : 'M_n) i1 i2,
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
move=> n A i1 i2 Di12 A12; pose r := 'I_n.
pose t := tperm i1 i2; pose tr s := (t * s)%g.
have trK : involutive tr by move=> s; rewrite /tr mulgA tperm2 mul1g.
have Etr: forall s, odd_perm (tr s) = even_perm s.
  by move=> s; rewrite odd_permM odd_tperm Di12.
rewrite /(\det _) (bigID (@even_perm _)) /=.
set S1 := \sum_(<- _ | _) _; set T := S1 + _.
rewrite -(addNr S1) addrC; congr (_ + _); rewrite {}/T {}/S1 -sum_opp.
rewrite (reindex tr) /=; last by exists tr => ? _.
symmetry; apply: eq_big => [s | s]; first by rewrite negbK Etr.
rewrite -topredE /= => seven; rewrite -mulNr Etr seven (negbET seven) expr1n.
congr (_ * _).
rewrite (reindex t) /=; last by exists (t : _ -> _) => i _; exact: tpermK.
apply: eq_bigr => i _; rewrite permM /t.
by case: tpermP => // ->; rewrite A12.
Qed.

Lemma determinant_tr : forall n (A : 'M_n), \det (\^t A) = \det A.
Proof.
move=> n A; pose r := 'I_n; pose ip p : 'S_n := p^-1.
rewrite /(\det _) (reindex ip) /=; last first.
  by exists ip => s _; rewrite /ip invgK.
apply: eq_bigr => s _; rewrite !odd_permV /= (reindex s).
  by congr (_ * _); apply: eq_bigr => i _; rewrite mxK permK.
by exists (s^-1 : _ -> _) => i _; rewrite ?permK ?permKV.
Qed.

Lemma determinant_perm : forall n (s : 'S_n), \det (\P s) = (-1) ^+s :> R.
Proof.
move=> n s; rewrite /(\det _) (bigD1 s) //=.
rewrite big1 => [|i _]; last by rewrite /= !mxK eqxx.
rewrite big1 => /= [|t Dst]; first by rewrite !simp.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (bigD1 i) // mulrCA /= mxK (negbET ist) simp.
by case/eqP: Dst; apply/permP => i; move/eqP: (Est i).
Qed.

Lemma determinant1 : forall n, \det \1_n = 1 :> R.
Proof.
move=> n; have:= @determinant_perm n 1%g; rewrite odd_perm1 => /= <-.
congr (\det _); symmetry; exact: perm_mx1.
Qed.

Lemma determinant_scale : forall n x (A : 'M_n),
  \det (x *s A) = x ^+n * \det A.
Proof.
move=> n x A; rewrite big_distrr /=; apply: eq_bigr => s _.
rewrite mulrCA; congr (_ * _).
rewrite -{10}[n]card_ord -prodr_const -big_split /=.
by apply: eq_bigr=> i _; rewrite mxK.
Qed.

Lemma determinantM : forall n (A B : 'M_n), \det (A *m B) = \det A * \det B.
Proof.
move=> n A B; rewrite big_distrl /=.
pose AB (f : {ffun _}) (s : 'S_n) i := A i (f i) * B (f i) (s i).
transitivity (\sum_f \sum_(s : 'S_n) (-1) ^+ s * \prod_i AB f s i).
  rewrite exchange_big; apply: eq_bigr => /= s _.
  rewrite -big_distrr /=; congr (_ * _).
  pose F i j := A i j * B j (s i); rewrite -(bigA_distr_bigA F) /=.
  by apply: eq_bigr => x _; rewrite mxK.
rewrite (bigID (fun f : {ffun _} => injectiveb f)) /= addrC big1 ?simp => [|f Uf].
  rewrite (reindex (fun s => pval s)); last first.
    have s0 : 'S_n := 1%g; pose uf (f : {ffun 'I_n -> 'I_n}) := uniq (val f).
    exists (insubd s0) => /= f Uf; first apply: val_inj; exact: insubdK.
  apply: eq_big => /= [s|s _]; rewrite ?(valP s) // big_distrr /=.
  rewrite (reindex (mulg s)); last first.
    by exists (mulg s^-1) => t _; rewrite ?mulKVg ?mulKg.
  apply: eq_bigr => t _; rewrite big_split /= mulrA mulrCA mulrA mulrCA mulrA.
  rewrite -signr_addb odd_permM !pvalE; congr (_ * _).
  rewrite (reindex s^-1); last first.
    by exists (s : _ -> _) => i _; rewrite ?permK ?permKV.
  by apply: eq_bigr => i _; rewrite permM permKV ?eqxx // -{3}[i](permKV s).
transitivity (\det (\matrix_(i, j) B (f i) j) * \prod_i A i (f i)).
  rewrite mulrC big_distrr /=; apply: eq_bigr => s _.
  rewrite mulrCA big_split //=; congr (_ * (_ * _)).
  by apply: eq_bigr => x _; rewrite mxK.
case/injectivePn: Uf => i1 [i2 Di12 Ef12].
by rewrite (alternate_determinant Di12) ?simp //= => j; rewrite !mxK Ef12.
Qed.

Lemma expand_cofactor : forall n (A : 'M_n) i j,
  cofactor A i j =
    \sum_(s : 'S_n | s i == j) (-1)^+s * \prod_(k | i != k) A k (s k).
Proof.
move=> n.
pose lsf i (s : 'S_(n.-1)) j k :=
  if unlift i k is Some k' then lift j (s k') else j.
have lsfE: forall i s j, (lsf i s j i = j)
                       * (forall k, lsf i s j (lift i k) = lift j (s k)).
- by split=> *; rewrite /lsf ?unlift_none ?liftK.
have inj_lsf : injective (lsf _ _ _).
  move=> i s j; apply: can_inj (lsf j s^-1 i) _ => k.
  by case: (unliftP i k) => [k'|] ->; rewrite !lsfE ?permK.
pose ls := perm_of (inj_lsf _ _ _).
have ls1 : forall i, ls i 1%g i = 1%g.
  move=> i; apply/permP => k.
  by case: (unliftP i k) => [k'|] ->; rewrite permE lsfE !perm1.
have lsM : forall i s j t k, (ls i s j * ls j t k)%g = ls i (s * t)%g k.
  move=> i s j t k; apply/permP=> l; rewrite permM !permE.
  by case: (unliftP i l) => [l'|] ->; rewrite !lsfE ?permM.
have sign_ls: forall s i j, (-1)^+(ls i s j) = (-1) ^+s * (-1)^+(i + j) :> R.
  pose nfp (s : 'S_(n.-1)) := [pred k | s k != k].
  move=> s i j; elim: {s}_.+1 {-2}s (ltnSn #|nfp s|) => // m IHm s Hm.
  case: (pickP (nfp s)) Hm => [k Dsk | s1 _ {m IHm}].
    rewrite ltnS (cardD1 k) [k \in _]Dsk => Hm.
    pose t := tperm k (fun_of_perm s^-1 k).
    rewrite -(mulKg t s) tpermV -(lsM _ _ i).
    rewrite 2!odd_permM 2!signr_addb -mulrA -{}IHm; last first.
      apply: {m} leq_trans Hm; apply: subset_leq_card; apply/subsetP=> k'.
      rewrite !inE /= inE /= permM /t (eq_sym k').
      case: tpermP=> [->|-> Ds|]; rewrite ?permKV; first by rewrite eqxx.
        by rewrite andbb; apply/eqP=> Dk; case/eqP: Ds; rewrite {1}Dk permKV.
      by move/eqP; rewrite eq_sym => ->.
    suffices ->: ls i t i = tperm (lift i k) (lift i (fun_of_perm s^-1 k)).
      by rewrite !odd_tperm (inj_eq (@lift_inj _ _)).
    apply/permP=> i'; rewrite permE.
    case: (unliftP i i') => [i''|] ->; rewrite lsfE.
      rewrite inj_tperm //; exact: lift_inj.
    case tpermP => //; move/eqP; case/idPn; exact: neq_lift.
  have ->: s = 1%g.
    by apply/permP=> k; rewrite perm1; move/eqP: (s1 k).
  rewrite odd_perm1 simp /=; without loss: i {s s1} j / j <= i.
    case: (leqP j i); first by auto.
    move/ltnW=> ij; move/(_ _ _ ij)=> Wji.
    rewrite -(mulgK (ls j 1%g i) (ls i  _ j)) lsM !(ls1,mul1g).
    by rewrite odd_permV addnC.
  move Dm: i.+1 => m; elim: m i Dm => // m IHm i [im].
  rewrite leq_eqVlt; case/predU1P=> [eqji|ltji].
    by rewrite (val_inj _ _ eqji) ls1 odd_perm1 /= -signr_odd odd_add addbb.
  have m'm: m.-1.+1 = m by rewrite -im (ltn_predK ltji).
  have ltm'n : m.-1 < n by rewrite m'm -im leq_eqVlt orbC (ltn_ord i).
  pose i' := Ordinal ltm'n; rewrite -{1}(mulg1 1%g) -(lsM _ _ i') odd_permM.
  rewrite signr_addb mulrC {}IHm; try by rewrite /= - 1?ltnS ?m'm // -im.
  rewrite im -m'm addSn -addn1 (exprn_addr _ _ 1); congr (_ * _).
  have{j ltji} ii' : i != i' by rewrite -val_eqE /= im /= -m'm eqn_leq ltnn.
  transitivity (((-1) ^+(tperm i i')) : R); last by rewrite odd_tperm ii'.
  congr (_ ^+(odd_perm _)); apply/permP => k.
  case: (unliftP i k) => [k'|] -> {k}; rewrite permE lsfE ?tpermL // perm1.
  apply: val_inj; rewrite permE /transpose (negbET (neq_lift _ _)) /pred1.
  rewrite fun_if -val_eqE /= im /bump; case mk': (m <= _).
    by rewrite eqn_leq ltnNge leq_eqVlt m'm mk' orbT andbF.
  by rewrite add0n leq_eqVlt m'm mk'; case: eqP => //= <-.
move=> A i0 j0; rewrite (reindex (fun s => ls i0 s j0)); last first.
  pose ulsf i (s : 'S_n) k' :=
    if unlift (s i) (s (lift i k')) is Some k then k else k'.
  have ulsfE: forall i (s : 'S_n) k',
      lift (s i) (ulsf i s k') = s (lift i k').
    rewrite /ulsf => i s k'; have:= neq_lift i k'.
    by rewrite -(inj_eq (@perm_inj _ s)); case/unlift_some=> ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1) _ => k'.
    by rewrite {1}/ulsf ulsfE !permK liftK.
  exists (fun s => perm_of (inj_ulsf s)) => [s _ | s].
    by apply/permP=> k'; rewrite permE /ulsf !permE !lsfE liftK.
  move/(s _ =P _) => si0; apply/permP=> k.
  by case: (unliftP i0 k) => [k'|] ->; rewrite permE lsfE // permE -si0 ulsfE.
rewrite /cofactor big_distrr /=.
apply: eq_big => [s | s _]; first by rewrite permE lsfE eqxx.
rewrite mulrCA mulrA -{}sign_ls; congr (_ * _).
case: (pickP {'I_(n.-1)}) => [k'0 _ | r'0]; last first.
  rewrite !big_pred0 // => k; apply/idP; case/unlift_some=> k'.
  by have:= r'0 k'.
rewrite (reindex (lift i0)).
  by apply: eq_big => [k | k _] /=; rewrite ?neq_lift // !mxK permE lsfE.
pose f k := if unlift i0 k is Some k' then k' else k'0.
by exists f; rewrite /f => k; [rewrite liftK | case/unlift_some=> ? ? ->].
Qed.

Lemma expand_determinant_row : forall n (A : 'M_n) i0,
  \det A = \sum_j A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
rewrite (partition_big (fun s : 'S_n => s i0) predT) //=.
apply: eq_bigr => j0 _; rewrite expand_cofactor big_distrr /=.
apply: eq_bigr => s; rewrite -topredE /=; move/eqP=> Dsi0.
rewrite mulrCA (bigID (pred1 i0)) /= big_pred1_eq Dsi0; congr (_ * (_ * _)).
by apply: eq_bigl => i; rewrite eq_sym.
Qed.

Lemma cofactor_tr : forall n (A : 'M_n) i j,
  cofactor (\^t A) i j = cofactor A j i.
Proof.
move=> n A i j; rewrite /cofactor addnC; congr (_ * _).
rewrite -tr_rem_row -tr_rem_col determinant_tr; congr (\det _).
by apply/matrixP=> ? ?; rewrite !mxK.
Qed.

Lemma expand_determinant_col : forall n (A : 'M_n) j0,
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -determinant_tr (expand_determinant_row _ j0).
by apply: eq_bigr => i _; rewrite cofactor_tr mxK.
Qed.

Lemma mulmx_adjr : forall n (A : 'M_n), A *m adjugate A = \Z (\det A).
Proof.
move=> n A; apply/matrixP=> i1 i2; rewrite !mxK; case Di: (i1 == i2).
  rewrite (eqP Di) (expand_determinant_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxK.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxK Di eq_refl.
rewrite -{2}(alternate_determinant (negbT Di) EBi12).
rewrite (expand_determinant_row _ i2); apply: eq_bigr => j _.
rewrite !mxK eq_refl; congr (_ * (_ * _)).
apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => i _.
by rewrite !mxK eq_sym -if_neg neq_lift.
Qed.

Lemma adjugate_tr : forall n (A : 'M_n), adjugate (\^t A) = \^t (adjugate A).
Proof. by move=> n A; apply/matrixP=> i j; rewrite !mxK cofactor_tr. Qed.

Lemma mulmx_adjl : forall n (A : 'M_n), adjugate A *m A =  \Z (\det A).
Proof.
move=> n A; apply: trmx_inj; rewrite tr_mulmx -adjugate_tr mulmx_adjr.
by rewrite determinant_tr trmxZ.
Qed.

End MatrixOnComRingProp.


Import Field.
Open Scope field_scope.

Section GenLinGrp.
Variables (K : field) (n : nat).

Notation Local "''M_' ( n )" := (matrix K n n) : matrix_scope.
Notation Local "''M_' n" := 'M_(n) : matrix_scope.
Notation Local "\mulmx" := (@mulmx K n n n) : matrix_scope.

Definition invmx := fun A : 'M_n => (\det A)^-1 *s \adj A.
Notation "A ^-1m" := (invmx A) (at level 2, format "A ^-1m") : matrix_scope.

Lemma mulVmx : forall A : 'M_n, \det A != 0 -> A *m A^-1m = \1.
Proof.
move=> A Ha.
by rewrite -scalemxAr mulmx_adjr -scalemx1 scalemxA mulfV ?scale1mx.
Qed.

Lemma mulmxV : forall A : 'M_n, \det A != 0 -> A^-1m *m A= \1.
Proof.
move=> A Ha.
by rewrite -scalemxAl mulmx_adjl -scalemx1 scalemxA mulfV ?scale1mx//.
Qed.

Lemma mulKmx : forall A : 'M_n,
  \det A != 0 -> cancel (\mulmx A) (\mulmx A^-1m).
Proof. by move=> A Ha B; rewrite mulmxA mulmxV// mul1mx. Qed.

Lemma mulmxK : forall (A : 'M_n),
  \det A != 0 -> cancel (\mulmx^~ A) (\mulmx^~ A^-1m).
Proof. by move=> A Ha B; rewrite -mulmxA mulVmx// mulmx1. Qed.

Lemma mulImx : forall A : 'M_n, \det A != 0 -> injective (\mulmx A).
Proof. move=> A Ha; exact: can_inj (mulKmx Ha). Qed.

Lemma mulmxI : forall A : 'M_n, \det A != 0 -> injective (\mulmx^~ A).
Proof. move=> A Ha; exact: can_inj (mulmxK Ha). Qed.

Lemma neq0_Dmx: forall A : 'M_n, \det A != 0 -> \det A^-1m != 0.
Proof.
move=> A Ha; rewrite determinant_scale.
move: (congr1 (@determinant _ n) (mulmx_adjl A));
 rewrite determinantM -scalemx1 determinant_scale determinant1 mulr1.
move/(congr1 (mul (\det A)^-1)); rewrite mulrCA mulfV// mulr1=> ->.
rewrite mulrCA -exprn_mull mulfV// exp1rn mulr1.
by apply: neq0I.
Qed.

Lemma neq0_Dmx_mul : forall A B : 'M_n,
 \det A != 0 -> \det B != 0 -> \det (A *m B) != 0.
Proof. by move=> *; rewrite determinantM; apply: neq0_mul. Qed.

Lemma invmxK : forall A : 'M_n, \det A != 0 -> (A^-1m)^-1m = A.
Proof.
move=> A Ha; apply: (mulmxI (neq0_Dmx Ha)).
by rewrite mulVmx// mulmxV//; apply: neq0_Dmx.
Qed.

Lemma invmx1 : \1^-1m = \1 :> 'M_n.
Proof.
rewrite -[\1^-1m]mul1mx mulVmx// determinant1;
apply/eqP; exact: nonzero1r.
Qed.

Lemma invmxI : forall A B : 'M_n,
 \det A != 0 -> \det B != 0 -> A^-1m = B^-1m -> A = B.
Proof. by move=> A B Ha Hb Hab; rewrite -(invmxK Ha) -(invmxK Hb) Hab. Qed.

Lemma invmx_mul : forall A B : 'M_n,
 \det A != 0 -> \det B != 0 -> (A *m B)^-1m = B^-1m *m A^-1m.
Proof.
move=> A B Ha Hb; apply: (mulImx (neq0_Dmx_mul Ha Hb)).
rewrite mulVmx; last exact: neq0_Dmx_mul.
by rewrite -mulmxA [B *m (_ *m _)]mulmxA mulVmx// mul1mx mulVmx.
Qed.

End GenLinGrp.

Unset Implicit Arguments.
