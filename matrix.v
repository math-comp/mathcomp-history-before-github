(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import finfun bigops ssralg groups perm signperm zmodp morphisms.

(* Require Import div connect finset zp. *)

Import GroupScope.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "''M_' n"       (at level 8, n at level 2, format "''M_' n").
Reserved Notation "''M_' ( n )"   (at level 8, only parsing).
Reserved Notation "''M_' ( m , n )" (at level 8, format "''M_' ( m ,  n )").

Reserved Notation "\matrix_ ( i , j ) E"
  (at level 36, E at level 36, i, j at level 50,
   format "\matrix_ ( i ,  j )  E").
Reserved Notation "\matrix_ ( i < m , j < n ) E"
  (at level 36, E at level 36, i, m, j, n at level 50,
   format "\matrix_ ( i  <  m ,  j  <  n )  E").
Reserved Notation "\matrix_ ( i , j < n ) E"
  (at level 36, E at level 36, i, j, n at level 50,
   format "\matrix_ ( i ,  j  <  n )  E").

Reserved Notation "x %:M"   (at level 8, format "x %:M").
Reserved Notation "x *m: A" (at level 40, format "x  *m:  A").
Reserved Notation "A *m B"  (at level 40, format "A  *m  B").
Reserved Notation "A ^T"    (at level 8, format "A ^T").
Reserved Notation "\tr A"   (at level 10, A at level 8, format "\tr  A").
Reserved Notation "\det A"  (at level 10, A at level 8, format "\det  A").
Reserved Notation "\adj A"  (at level 10, A at level 8, format "\adj  A").

Delimit Scope matrix_scope with M.

Notation Local simp := (Monoid.Theory.simpm, oppr0).

Open Local Scope ring_scope.
Open Local Scope matrix_scope.

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

(* Basic linear algebra (matrices).                                       *)
(*   We use dependent types (ordinals) for the indices so that ranges are *)
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

Notation "''M_' n"  := (matrix _ n n) : type_scope.
Notation "''M_' ( n )" := 'M_n (only parsing) : type_scope.
Notation "''M_' ( m , n )" := (matrix _ m n) : type_scope.

Notation "\matrix_ ( i < m , j < n ) E" :=
  (@matrix_of_fun _ m n (fun i j => E)) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j < n ) E" :=
  (\matrix_(i < n, j < n) E) (only parsing) : ring_scope.

Notation "\matrix_ ( i , j ) E" := (\matrix_(i < _, j < _) E) : ring_scope.

Definition matrix_eqMixin (R : eqType) m n :=
  CanEqMixin (@mx_valK R m n).
Canonical Structure matrix_eqType R m n:=
  Eval hnf in EqType (matrix_eqMixin R m n).
Definition matrix_choiceMixin (R : choiceType) m n :=
  CanChoiceMixin (@mx_valK R m n).
Canonical Structure matrix_choiceType R m n :=
  Eval hnf in ChoiceType (matrix_choiceMixin R m n).

Section Slicing.

Variable R : Type.

Definition mx_row m n i0 (A : 'M_(m, n)) :=
  \matrix_(i < 1, j < n) (A i0 j : R).
Definition mx_col m n j0 (A : 'M_(m, n)) :=
  \matrix_(i < m, j < 1) (A i j0 : R).
Definition mx_row' m n i0 (A : 'M_(m, n)) :=
  \matrix_(i, j) (A (lift i0 i) j : R).
Definition mx_col' m n j0 (A : 'M_(m, n)) :=
  \matrix_(i, j) (A i (lift j0 j) : R).

Definition rswap m n (A : 'M_(m, n)) i1 i2 :=
  \matrix_(i, j) (A (tperm i1 i2 i) j : R). 
    
Definition cswap m n (A : 'M_(m, n)) i1 i2 :=
  \matrix_(i, j) (A i (tperm i1 i2 j) : R). 
    
Definition trmx m n (A : 'M_(m, n)) := \matrix_(i, j) (A j i : R).

Lemma trmxK : forall m n, cancel (@trmx m n) (@trmx n m).
Proof. by move=> m n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_inj : forall m n, injective (@trmx m n).
Proof. move=> m n; exact: can_inj (@trmxK m n). Qed.

Notation "A ^T" := (trmx A) : ring_scope.

Lemma trmx_row : forall m n i0 (A : 'M_(m, n)),
  (mx_row i0 A)^T = mx_col i0 A^T.
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_row' : forall m n i0 (A : 'M_(m, n)),
  (mx_row' i0 A)^T = mx_col' i0 A^T.
Proof. by move=> m n i0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_col : forall m n j0 (A : 'M_(m, n)),
  (mx_col j0 A)^T = mx_row j0 A^T.
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_col' : forall m n j0 (A : 'M_(m, n)),
  (mx_col' j0 A)^T = mx_row' j0 A^T.
Proof. by move=> m n j0 A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_cswap : forall m n (A : 'M_(m, n)) i1 i2, 
  (cswap A i1 i2)^T = rswap A^T i1 i2. 
Proof. by move=> m n A i1 i2; apply/matrixP=> i j; rewrite !mxE. Qed. 

Lemma trmx_rswap : forall m n (A : 'M_(m, n)) i1 i2, 
  (rswap A i1 i2)^T = cswap A^T i1 i2. 
Proof. by move=> m n A i1 i2; apply: trmx_inj; rewrite trmx_cswap !trmxK. Qed.

Lemma mx_row_id : forall n (A : 'M_(1, n)), mx_row 0 A = A.
Proof. by move=> n A; apply/matrixP=> i j; rewrite mxE [i]ord1. Qed.

Lemma mx_row_eq : forall m1 m2 n i1 i2 (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)),
  mx_row i1 A1 = mx_row i2 A2 -> A1 i1 =1 A2 i2.
Proof.
move=> m1 m2 n i1 i2 A1 A2; move/matrixP=> eqA12 j.
by have:= eqA12 0 j; rewrite !mxE.
Qed.

Lemma mx_row'_eq : forall m n i0 (A B : 'M_(m, n)),
  mx_row' i0 A = mx_row' i0 B -> {in predC1 i0, A =2 B}.
Proof.
move=> m n i0 A B; move/matrixP=> eqAB' i.
rewrite !inE eq_sym; case/unlift_some=> i' -> _  j.
by have:= eqAB' i' j; rewrite !mxE.
Qed.

Section CutPaste.

Variables m n1 n2 : nat.

(* The shape of the (dependent) width parameter of the type of A *)
(* determines where the cut is made! *)

Definition lcutmx (A : 'M_(m, n1 + n2)):=
  \matrix_(i < m, j < n1) (A i (lshift n2 j) : R).

Definition rcutmx (A : 'M_(m, n1 + n2)) :=
  \matrix_(i < m, j < n2) (A i (rshift n1 j) : R).

Definition pastemx (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) :=
   \matrix_(i < m, j < n1 + n2)
      (match split j with inl j1 => A1 i j1 | inr j2 => A2 i j2 end : R).

Lemma pastemxEl : forall A1 A2 i j, pastemx A1 A2 i (lshift n2 j) = A1 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inl _ _)). Qed.
  
Lemma pastemxEr : forall A1 A2 i j, pastemx A1 A2 i (rshift n1 j) = A2 i j.
Proof. by move=> A1 A2 i j; rewrite mxE (unsplitK (inr _ _)). Qed.

Lemma pastemxKl : forall A1 A2, lcutmx (pastemx A1 A2) = A1.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE pastemxEl. Qed.

Lemma pastemxKr : forall A1 A2, rcutmx (pastemx A1 A2) = A2.
Proof. by move=> A1 A2; apply/matrixP=> i j; rewrite mxE pastemxEr. Qed.

Lemma cutmxK : forall A, pastemx (lcutmx A) (rcutmx A) = A.
Proof.
move=> A; apply/matrixP=> i j; rewrite !mxE.
case: splitP => k Dk //=; rewrite !mxE //=; congr (A _ _); exact: val_inj.
Qed.

End CutPaste.

Lemma mx_row_paste : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  mx_row i0 (pastemx A1 A2) = pastemx (mx_row i0 A1) (mx_row i0 A2).
Proof.
move=> m n1 n2 i0 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: (split j) => j'; rewrite mxE.
Qed.

Lemma mx_row'_paste : forall m n1 n2 i0 (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
  mx_row' i0 (pastemx A1 A2) = pastemx (mx_row' i0 A1) (mx_row' i0 A2).
Proof.
move=> m n1 n2 i0 A1 A2; apply/matrixP=> i j; rewrite !mxE.
by case: (split j) => j'; rewrite mxE.
Qed.

Lemma mx_col_lshift : forall m n1 n2 j1 (A1 : 'M_(m, n1)) A2,
  mx_col (lshift n2 j1) (pastemx A1 A2) = mx_col j1 A1.
Proof.
by move=> m n1 n2 j1 A1 A2; apply/matrixP=> i j; rewrite !(pastemxEl, mxE).
Qed.

Lemma mx_col_rshift : forall m n1 n2 j2 A1 (A2 : 'M_(m, n2)),
  mx_col (rshift n1 j2) (pastemx A1 A2) = mx_col j2 A2.
Proof.
by move=> m n1 n2 j2 A1 A2; apply/matrixP=> i j; rewrite !(pastemxEr, mxE).
Qed.

Lemma mx_col'_lshift : forall m n1 n2 j1 (A1 : 'M_(m, n1.+1)) A2,
  mx_col' (lshift n2 j1) (pastemx A1 A2) = pastemx (mx_col' j1 A1) A2.
Proof.
move=> m n1 n2 j1 A1 A2; apply/matrixP=> i /= j; symmetry; rewrite 2!mxE.
case: splitP => j' def_j'.
  rewrite mxE -(pastemxEl _ A2); congr (pastemx _ _ _); apply: ord_inj.
  by rewrite /= def_j'.
rewrite -(pastemxEr A1); congr (pastemx _ _ _); apply: ord_inj => /=.
by rewrite /bump def_j' -ltnS -addSn ltn_addr.
Qed.

Lemma mx_col'_rcast : forall n1 n2, 'I_n2 -> (n1 + n2.-1)%N = (n1 + n2).-1.
Proof. by move=> n1 n2 [j]; move/ltn_predK <-; rewrite addnS. Qed.

Lemma paste_mx_col' : forall m n1 n2 j2 A1 (A2 : 'M_(m, n2)),
  pastemx A1 (mx_col' j2 A2) 
    = eq_rect _ (matrix R m) (mx_col' (rshift n1 j2) (pastemx A1 A2))
              _ (esym (mx_col'_rcast n1 j2)).
Proof.
move=> m n1 n2 j2 A1 A2; apply/matrixP=> i /= j; rewrite mxE.
case: splitP => j' def_j'; case: (n1 + n2.-1)%N / (esym _) => /= in j def_j' *.
  rewrite mxE -(pastemxEl _ A2); congr (pastemx _ _ _); apply: ord_inj.
  by rewrite /= def_j' /bump leqNgt ltn_addr.
rewrite 2!mxE -(pastemxEr A1); congr (pastemx _ _ _ _); apply: ord_inj => /=.
by rewrite def_j' /bump leq_add2l addnCA.
Qed.

Lemma mx_col'_rshift : forall m n1 n2 j2 A1 (A2 : 'M_(m, n2)),
  mx_col' (rshift n1 j2) (pastemx A1 A2) 
    = eq_rect _ (matrix R m) (pastemx A1 (mx_col' j2 A2))
              _ (mx_col'_rcast n1 j2).
Proof.
move=> m n1 n2 j2 A1 A2; rewrite paste_mx_col'.
by case: _.-1 / (mx_col'_rcast n1 j2) {A1 A2}(mx_col' _ _).
Qed.

Section Block.

Variables m1 m2 n1 n2 : nat.

Definition block_mx Aul Aur All Alr : 'M_(m1 + m2, n1 + n2) :=
  (pastemx (pastemx Aul Aur)^T (pastemx All Alr)^T)^T.

Section CutBlock.

Variable A : matrix R (m1 + m2) (n1 + n2).

Definition ulsubmx := lcutmx (lcutmx A^T)^T.
Definition ursubmx := rcutmx (lcutmx A^T)^T.
Definition llsubmx := lcutmx (rcutmx A^T)^T.
Definition lrsubmx := rcutmx (rcutmx A^T)^T.

Lemma submxK : block_mx ulsubmx ursubmx llsubmx lrsubmx = A.
Proof. by rewrite /block_mx !(cutmxK, trmxK). Qed.

End CutBlock.

Section PasteBlock.

Variables (Aul : matrix R m1 n1) (Aur : matrix R m1 n2).
Variables (All : matrix R m2 n1) (Alr : matrix R m2 n2).

Let A := block_mx Aul Aur All Alr.

Lemma block_mxEul : forall i j, A (lshift m2 i) (lshift n2 j) = Aul i j.
Proof. by move=> i j; rewrite mxE pastemxEl mxE pastemxEl. Qed.
Lemma block_mxKul : ulsubmx A = Aul. 
Proof. by rewrite /ulsubmx trmxK pastemxKl trmxK pastemxKl. Qed.

Lemma block_mxEur : forall i j, A (lshift m2 i) (rshift n1 j) = Aur i j.
Proof. by move=> i j; rewrite mxE pastemxEl mxE pastemxEr. Qed.
Lemma block_mxKur : ursubmx A = Aur. 
Proof. by rewrite /ursubmx trmxK pastemxKl trmxK pastemxKr. Qed.

Lemma block_mxEll : forall i j, A (rshift m1 i) (lshift n2 j) = All i j.
Proof. by move=> i j; rewrite mxE pastemxEr mxE pastemxEl. Qed.
Lemma block_mxKll : llsubmx A = All. 
Proof. by rewrite /llsubmx trmxK pastemxKr trmxK pastemxKl. Qed.

Lemma block_mxElr : forall i j, A (rshift m1 i) (rshift n1 j) = Alr i j.
Proof. by move=> i j; rewrite mxE pastemxEr mxE pastemxEr. Qed.
Lemma block_mxKlr : lrsubmx A = Alr. 
Proof. by rewrite /lrsubmx trmxK pastemxKr trmxK pastemxKr. Qed.

End PasteBlock.

End Block.

Section TrBlock.

Variables m1 m2 n1 n2 : nat.

Section TrCut.

Variable A : matrix R (m1 + m2) (n1 + n2).

Lemma trmx_ulsub : (ulsubmx A)^T =  ulsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_ursub : (ursubmx A)^T =  llsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_llsub : (llsubmx A)^T =  ursubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_lrsub : (lrsubmx A)^T = lrsubmx A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End TrCut.

Lemma trmx_block : forall Aul Aur All Alr,
 (block_mx Aul Aur All Alr)^T =
    block_mx Aul^T All^T Aur^T Alr^T :> 'M_(n1 + n2, m1 + m2).
Proof.
move=> Aul Aur All Alr; rewrite -[_^T]submxK.
rewrite -trmx_ulsub -trmx_ursub -trmx_llsub -trmx_lrsub.
by rewrite block_mxKul block_mxKur block_mxKll block_mxKlr.
Qed.

End TrBlock.

End Slicing.

Notation "A ^T" := (trmx A) : ring_scope.
Prenex Implicits lcutmx rcutmx ulsubmx ursubmx llsubmx lrsubmx.

(* Definition of operations for matrices over a ring *)
Section MatrixOpsDef.

Variable R : ringType.

Section ZmodOps.
(* The Zmodule structure *)

Variables m n : nat.
Implicit Types A B C : matrix R m n.

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

(* Vector space structure... pending the definition *)

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

(* Basis... *)

Definition delta_mx i0 j0 :=
  \matrix_(i < m, j < n) (((i == i0) && (j == j0))%:R : R).

Lemma matrix_sum_delta : forall A,
  A = \sum_(i < m) \sum_(j < n) A i j *m: delta_mx i j.
Proof.
move=> A; apply/matrixP=> i j.
rewrite summxE (bigD1 i) // summxE (bigD1 j) //= !mxE.
rewrite !eqxx !big1 ?simp //= => [i' ii' | j' jj'].
  by rewrite summxE big1 // => j' _; rewrite !mxE eq_sym (negbTE ii') simp.
by rewrite !mxE eqxx eq_sym (negbTE jj') simp.
Qed.

End ZmodOps.

Notation "x *m: A" := (scalemx x A) : ring_scope.

Lemma trmx0 : forall m n, 0^T = 0 :> matrix R n m.
Proof. by move=> m n; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_add : forall m n A B, (A + B)^T = A^T + B^T :> matrix R n m.
Proof. by move=> m n A B; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_scale : forall m n a A, (a *m: A)^T = a *m: A^T :> matrix R n m.
Proof. by move=> m n a A; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mx_row0 : forall m n i0, @mx_row R m n i0 0 = 0.
Proof. by move=> m n i0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mx_col0 : forall m n j0, @mx_col R m n j0 0 = 0.
Proof. by move=> m n j0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mx_row'0 : forall m n i0, @mx_row' R m n i0 0 = 0.
Proof. by move=> m n i0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma mx_col'0 : forall m n j0, @mx_col' R m n j0 0 = 0.
Proof. by move=> m n j0; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma pastemx0 : forall m n1 n2,
  pastemx 0 0 = 0 :> matrix R m (n1 + n2).
Proof.
move=> m n1 n2; apply/matrixP=> i j.
by rewrite !mxE; case: split=> i'; rewrite !mxE.
Qed.

Lemma addmx_paste : forall m n1 n2 A1 A2 B1 B2,
  pastemx A1 A2 + pastemx B1 B2 = pastemx (A1 + B1) (A2 + B2)
                              :> matrix R m (n1 + n2).
Proof.
move=> m n1 n2 A1 A2 B1 B2; apply/matrixP=> i j.
by rewrite !mxE; case: split=> i'; rewrite !mxE.
Qed.

Lemma scalemx_paste : forall m n1 n2 a A1 A2,
  a *m: pastemx A1 A2 = pastemx (a *m: A1) (a *m: A2) :> matrix R m (n1 + n2).
Proof.
move=> m n1 n2 a A1 A2; apply/matrixP=> i j.
by rewrite !mxE; case: split=> i'; rewrite !mxE.
Qed.

Lemma block_mx0 : forall m1 m2 n1 n2,
  block_mx 0 0 0 0 = 0 :> matrix R (m1 + m2) (n1 + n2).
Proof. by move=> m1 m2 n1 n2; rewrite /block_mx !(pastemx0, trmx0). Qed.

Lemma addmx_block : forall m1 m2 n1 n2 Aul Aur All Alr Bul Bur Bll Blr,
  block_mx Aul Aur All Alr + block_mx Bul Bur Bll Blr
    = block_mx (Aul + Bul) (Aur + Bur) (All + Bll) (Alr + Blr)
    :> matrix R (m1 + m2) (n1 + n2).
Proof.
move=> m1 m2 n1 n2 Aul Aur All Alr Bul Bur Bll Blr.
by rewrite /block_mx !(addmx_paste, (I, trmx_add)).
Qed.

Lemma scalemx_block : forall m1 m2 n1 n2 a Aul Aur All Alr,
  a *m: block_mx Aul Aur All Alr
     = block_mx (a *m: Aul) (a *m: Aur) (a *m: All) (a *m: Alr)
    :> matrix R (m1 + m2) (n1 + n2).
Proof.
move=> m1 m2 n1 n2 a Aul Aur All Alr.
by rewrite /block_mx !(scalemx_paste, (I, trmx_scale)).
Qed.

(* The graded ring structure *)

Definition scalar_mx n x := \matrix_(i , j < n) (if i == j then x else 0 : R).
Definition mulmx m n p (A : 'M_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i < m, k < p) \sum_(j < n) (A i j * B j k : R).

Notation "x %:M" := (scalar_mx _ x) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.

Lemma scalar_mx0 : forall n, 0%:M = 0 :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxE if_same. Qed.

Lemma scalar_mx_opp : forall n a, (- a)%:M = - a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE (fun_if -%R) oppr0. Qed.

Lemma scalar_mx_add : forall n a b, (a + b)%:M = a%:M + b%:M :> 'M_n.
Proof.
move=> n a b; apply/matrixP=> i j; rewrite !mxE.
by case: (i == j); rewrite ?simp.
Qed.

Lemma mulmx_scalar : forall m n a A, a%:M *m A = a *m: A :> 'M_(m, n).
Proof.
move=> m n a A; apply/matrixP=> i j.
rewrite !mxE (bigD1 i) //= !mxE eqxx big1 ?simp // => i' i'i.
by rewrite mxE eq_sym -if_neg i'i simp.
Qed.

Lemma scalar_mx_mul : forall n a b, (a * b)%:M = a%:M *m b%:M :> 'M_n.
Proof.
move=> n a b; apply/matrixP=> i j; rewrite mulmx_scalar !mxE.
by case: (i == j); rewrite ?simp.
Qed.

Lemma trmx_scalar : forall n a, (a%:M)^T = a%:M :> 'M_n.
Proof. by move=> n a; apply/matrixP=> i j; rewrite !mxE eq_sym. Qed.

Lemma mul1mx : forall m n A, 1%:M *m A = A :> 'M_(m, n).
Proof. by move=> m n A; rewrite mulmx_scalar scale1mx. Qed.

Lemma mulmx_addl : forall m n p (A1 A2 : 'M_(m, n)) (B : 'M_(n, p)),
  (A1 + A2) *m B = A1 *m B + A2 *m B.
Proof.
move=> m n p A1 A2 B; apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite !mxE -mulr_addl.
Qed.

Lemma scalemx_add : forall n a1 a2, (a1 + a2)%:M = a1%:M + a2%:M :> 'M_n.
Proof.
move=> n a1 a2; apply/matrixP=> i j.
by rewrite !mxE; case: (i == j); rewrite ?simp.
Qed.

Lemma scalemxAl : forall m n p a (A : 'M_(m, n)) (B : 'M_(n, p)),
  a *m: (A *m B) = (a *m: A) *m B.
Proof.
move=> m n p a A B; apply/matrixP=> i k; rewrite !mxE big_distrr /=.
by apply: eq_bigr => j _; rewrite mulrA mxE.
Qed.

Lemma mul0mx : forall m n p (A : 'M_(n, p)), 0 *m A = 0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k; rewrite !mxE big1 ?simp //= => j _.
by rewrite mxE simp.
Qed.

Lemma mulmx0 : forall m n p (A : 'M_(m, n)), A *m 0 = 0 :> 'M_(m, p).
Proof.
move=> m n p A; apply/matrixP=> i k; rewrite !mxE big1 ?simp //= => j _.
by rewrite mxE simp.
Qed.

Lemma mulmx1 : forall m n (A : 'M_(m, n)), A *m 1%:M = A.
Proof.
move=> m n A; apply/matrixP=> i k; rewrite !mxE.
rewrite (bigD1 k) //= !mxE eqxx mulr1 big1 ?simp //= => j ji.
by rewrite mxE (negbTE ji) simp.
Qed.

Lemma mulmx_addr : forall m n p (A : 'M_(m, n)) (B1 B2 : 'M_(n, p)),
  A *m (B1 + B2) = A *m B1 + A *m B2.
Proof.
move=> m n p A B1 B2; apply/matrixP=> i k; rewrite !mxE -big_split /=.
by apply: eq_bigr => j _; rewrite mxE mulr_addr.
Qed.

Lemma mulmxA : forall m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)),
  A *m (B *m C) = A *m B *m C.
Proof.
move=> m n p q A B C; apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j * (B j k * C k l)))).
  by apply: eq_bigr => j _; rewrite mxE big_distrr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE big_distrl /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

Definition perm_mx n (s : 'S_n) :=
  \matrix_(i, j) (if s i == j then 1 else 0 : R).

Definition tperm_mx n i1 i2 := @perm_mx n (tperm i1 i2). 

Lemma trmx_perm : forall n (s : 'S_n), (perm_mx s)^T = perm_mx s^-1.
Proof.
by move=> n s; apply/matrixP=> i j; rewrite !mxE (canF_eq (permK _)) eq_sym.
Qed.

Lemma trmx_tperm : forall n i1 i2, (@tperm_mx n i1 i2)^T = tperm_mx i1 i2.
Proof. by move=> n i1 i2; rewrite trmx_perm tpermV. Qed.

Lemma mulmx_perm : forall n (s t : 'S_n),
  perm_mx s *m perm_mx t = perm_mx (s * t).
Proof.
move=> n s t; apply/matrixP=> i j; rewrite !mxE (bigD1 (s i)) //= !mxE eqxx.
rewrite simp -permM big1 /= => [|k ne_k_si]; first by rewrite addrC simp.
by rewrite mxE /= eq_sym (negbTE ne_k_si) simp.
Qed.

Lemma mul_tperm_mx : forall m n (A : matrix R m n) i1 i2, 
  (tperm_mx i1 i2) *m A = rswap A i1 i2.
Proof. 
move=> m n' A i1 i2; apply/matrixP=> i j.
rewrite !mxE (bigD1 (tperm i1 i2 i)) ?big1 //= => [|k ne_k_j].
  by rewrite mxE eqxx addr0 mul1r. 
by rewrite mxE eq_sym -if_neg ne_k_j mul0r. 
Qed. 

Lemma perm_mx1 : forall n, perm_mx 1%g = 1%:M :> 'M_n.
Proof. by move=> n; apply/matrixP=> i j; rewrite !mxE perm1. Qed.

(* The trace, in 1/4 line. *)
Definition mx_trace n (A : 'M_n) := \sum_i A i i : R.
Notation "'\tr' A" := (mx_trace A) : ring_scope.

Lemma mx_trace0 : forall n, \tr (0 : 'M_n) = 0.
Proof. by move=> n; apply: big1 => i _; rewrite mxE. Qed.

Lemma mx_trace_scale : forall n a (A : 'M_n), \tr (a *m: A) = a * \tr A.
Proof.
by move=> n a A; rewrite big_distrr; apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma mx_trace_scalar : forall n a, \tr (a%:M : 'M_n) = a *+ n.
Proof.
move=> n a; rewrite -{5}(card_ord n) -sumr_const; apply: eq_bigr => i _.
by rewrite mxE eqxx.
Qed.

Lemma mx_trace_add : forall n A B, \tr (A + B : 'M_n) = \tr A + \tr B.
Proof.
by move=> n A B; rewrite -big_split; apply: eq_bigr => i _; rewrite mxE.
Qed.

Lemma mx_trace_tr : forall n (A : 'M_n), \tr A^T = \tr A.
Proof. by move=> n A; apply: eq_bigr=> i _; rewrite mxE. Qed.

Lemma mx_trace_block : forall n1 n2 Aul Aur All Alr,
  \tr (block_mx Aul Aur All Alr : 'M_(n1 + n2)) = \tr Aul + \tr Alr.
Proof.
move=> n1 n2 Aul Aur All Alr; rewrite /(\tr _) big_split_ord /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite (block_mxEul, block_mxElr).
Qed.

Lemma mulmx_paste : forall m n p1 p2 (A : 'M_(m, n)) B1 B2,
  A *m (pastemx B1 B2) = pastemx (A *m B1) (A *m B2) :> 'M_(m, p1 + p2).
Proof.
move=> m n p1 p2 A B1 B2; apply/matrixP=> i k; rewrite !mxE.
by case defk: (split k) => [k1 | k2]; 
   rewrite mxE; apply: eq_bigr => j _; rewrite mxE defk.
Qed.

Lemma dotmx_paste : forall m n1 n2 p A1 A2 B1 B2,
  (pastemx A1 A2 : 'M_(m, n1 + n2)) *m (pastemx B1 B2 : 'M_(p, n1 + n2))^T
    = A1 *m B1^T + A2 *m B2^T.
Proof.
move=> m n1 n2 p A1 A2 B1 B2.
apply/matrixP=> i k; rewrite !mxE big_split_ord /=.
by congr (_ + _); apply: eq_bigr => j _; rewrite !(pastemxEl, pastemxEr, mxE).
Qed.

Section MatrixRing.

Variable n : pos_nat.

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

End MatrixRing.
 
End MatrixOpsDef.

Notation "a *m: A" := (scalemx a A) : ring_scope.
Notation "a %:M" := (scalar_mx _ a) : ring_scope.
Notation "A *m B" := (mulmx A B) : ring_scope.
Notation "\tr A" := (mx_trace A) : ring_scope.

Section TrMul.

Variable R : ringType.

Lemma trmx_mul_rev : forall m n p (A : matrix R m n) (B : matrix R n p),
  (A *m B)^T = (B^T : matrix (RevRingType R) p n) *m A^T.
Proof.
move=> m n p A B; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite !mxE.
Qed.

Lemma mulmx_block : forall m1 m2 n1 n2 p1 p2 Aul Aur All Alr Bul Bur Bll Blr,
  (block_mx Aul Aur All Alr : matrix R (m1 + m2) (n1 + n2))
   *m (block_mx Bul Bur Bll Blr : 'M_(n1 + n2, p1 + p2))
    = block_mx (Aul *m Bul + Aur *m Bll) (Aul *m Bur + Aur *m Blr)
               (All *m Bul + Alr *m Bll) (All *m Bur + Alr *m Blr).
Proof.
move=> m1 m2 n1 n2 p1 p2 Aul Aur All Alr Bul Bur Bll Blr.
rewrite -[_ *m _]trmxK trmx_mul_rev trmxK trmx_block dotmx_paste !trmxK.
by rewrite !mulmx_paste -!trmx_mul_rev !mulmx_paste trmx_add addmx_block.
Qed.

Lemma mul_mx_tperm : forall m n (A : matrix R m n) i1 i2, 
  A *m (tperm_mx R i1 i2) = cswap A i1 i2.
Proof.
move=> m n A i1 i2; apply: trmx_inj.
by rewrite trmx_mul_rev trmx_tperm mul_tperm_mx trmx_cswap.
Qed.    

End TrMul.

Section ComMatrix.

Variable R : comRingType.

Lemma trmx_mul : forall m n p (A : matrix R m n) (B : 'M_(n, p)),
  (A *m B)^T = B^T *m A^T.
Proof.
move=> m n p A B; rewrite trmx_mul_rev; apply/matrixP=> k i; rewrite !mxE.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Lemma scalemxAr : forall m n p a (A : matrix R m n) (B : 'M_(n, p)),
  a *m: (A *m B) = A *m (a *m: B).
Proof.
move=> m n p a A B.
by apply: trmx_inj; rewrite !(trmx_scale, trmx_mul) scalemxAl.
Qed.

Lemma scalar_mx_comm : forall (n : pos_nat) a (A : matrix R n n),
  GRing.comm A a%:M.
Proof.
move=> n a A; apply: trmx_inj; rewrite trmx_mul trmx_scalar -mulmxE.
by rewrite !mulmx_scalar trmx_scale.
Qed.

Lemma mx_trace_mulC : forall m n (A : matrix R m n) B,
  \tr (A *m B) = \tr (B *m A).
Proof.
move=> m n A B; transitivity (\sum_i \sum_j A i j * B j i).
  by apply: eq_bigr => i _; rewrite mxE.
rewrite exchange_big; apply: eq_bigr => i _ /=; rewrite mxE.
apply: eq_bigr => j _; exact: mulrC.
Qed.

(* The determinant, in one line. *)
Definition determinant n (A : 'M_n) :=
  \sum_(s : 'S_n) (-1) ^+ s * \prod_i A i (s i) : R.

Notation "'\det' A" := (determinant A).

Definition cofactor n A (i j : 'I_n) : R :=
  (-1) ^+ (i + j) * \det (mx_row' i (mx_col' j A)).

Definition adjugate n A := \matrix_(i, j < n) (cofactor A j i : R).

Lemma determinant_multilinear : forall n (A B C : 'M_n) i0 b c,
    mx_row i0 A = b *m: mx_row i0 B + c *m: mx_row i0 C ->
    mx_row' i0 B = mx_row' i0 A ->
    mx_row' i0 C = mx_row' i0 A ->
  \det A = b * \det B + c * \det C :> R.
Proof.
move=> n A B C i0 b c; rewrite -[_ + _]mx_row_id; move/mx_row_eq=> ABC.
move/mx_row'_eq=> BA; move/mx_row'_eq=> CA.
rewrite !big_distrr -big_split; apply: eq_bigr => s _ /=.
rewrite -!(mulrCA (_ ^+s)) -mulr_addr; congr (_ * _).
rewrite !(bigD1 i0 (_ : predT i0)) //= {}ABC !mxE mulr_addl !mulrA.
by congr (_ * _ + _ * _); apply: eq_bigr => i i0i; rewrite ?BA ?CA.
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
rewrite -(addNr S1) addrC; congr (_ + _); rewrite {}/T {}/S1 -sumr_opp.
rewrite (reindex tr) /=; last by exists tr => ? _.
symmetry; apply: eq_big => [s | s seven]; first by rewrite negbK Etr.
rewrite -mulNr Etr seven (negbTE seven) expr1; congr (_ * _).
rewrite (reindex t) /=; last by exists (t : _ -> _) => i _; exact: tpermK.
apply: eq_bigr => i _; rewrite permM /t.
by case: tpermP => // ->; rewrite A12.
Qed.

Lemma det_trmx : forall n (A : 'M_n), \det A^T = \det A.
Proof.
move=> n A; pose r := 'I_n; pose ip p : 'S_n := p^-1%g.
rewrite /(\det _) (reindex ip) /=; last first.
  by exists ip => s _; rewrite /ip invgK.
apply: eq_bigr => s _; rewrite !odd_permV /= (reindex s).
  by congr (_ * _); apply: eq_bigr => i _; rewrite mxE permK.
by exists (s^-1%g : _ -> _) => i _; rewrite ?permK ?permKV.
Qed.

Lemma det_perm_mx : forall n (s : 'S_n), \det (perm_mx R s) = (-1) ^+s.
Proof.
move=> n s; rewrite /(\det _) (bigD1 s) //=.
rewrite big1 => [|i _]; last by rewrite /= !mxE eqxx.
rewrite big1 => /= [|t Dst]; first by rewrite !simp.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (bigD1 i) // mulrCA /= mxE (negbTE ist) simp.
by case/eqP: Dst; apply/permP => i; move/eqP: (Est i).
Qed.

Lemma det1 : forall n, \det (1%:M : matrix R n n) = 1.
Proof. by move=> n; rewrite -perm_mx1 det_perm_mx odd_perm1. Qed.

Lemma det_scalemx : forall n x (A : 'M_n),
  \det (x *m: A) = x ^+ n * \det A.
Proof.
move=> n x A; rewrite big_distrr /=; apply: eq_bigr => s _.
rewrite mulrCA; congr (_ * _).
rewrite -{10}[n]card_ord -prodr_const -big_split /=.
by apply: eq_bigr=> i _; rewrite mxE.
Qed.

Lemma det_mulmx : forall n (A B : 'M_n), \det (A *m B) = \det A * \det B.
Proof.
move=> n A B; rewrite big_distrl /=.
pose AB (f : {ffun _}) (s : 'S_n) i := A i (f i) * B (f i) (s i).
transitivity (\sum_f \sum_(s : 'S_n) (-1) ^+ s * \prod_i AB f s i).
  rewrite exchange_big; apply: eq_bigr => /= s _.
  rewrite -big_distrr /=; congr (_ * _).
  pose F i j := A i j * B j (s i); rewrite -(bigA_distr_bigA F) /=.
  by apply: eq_bigr => x _; rewrite mxE.
rewrite (bigID (fun f : {ffun _} => injectiveb f)) /= addrC big1 ?simp => [|f Uf].
  rewrite (reindex (fun s => pval s)); last first.
    have s0 : 'S_n := 1%g; pose uf (f : {ffun 'I_n -> 'I_n}) := uniq (val f).
    exists (insubd s0) => /= f Uf; first apply: val_inj; exact: insubdK.
  apply: eq_big => /= [s|s _]; rewrite ?(valP s) // big_distrr /=.
  rewrite (reindex (mulg s)); last first.
    by exists (mulg s^-1%g) => t _; rewrite ?mulKVg ?mulKg.
  apply: eq_bigr => t _; rewrite big_split /= mulrA mulrCA mulrA mulrCA mulrA.
  rewrite -signr_addb odd_permM !pvalE; congr (_ * _).
  rewrite (reindex s^-1%g); last first.
    by exists (s : _ -> _) => i _; rewrite ?permK ?permKV.
  by apply: eq_bigr => i _; rewrite permM permKV ?eqxx // -{3}[i](permKV s).
transitivity (\det (\matrix_(i, j) B (f i) j) * \prod_i A i (f i)).
  rewrite mulrC big_distrr /=; apply: eq_bigr => s _.
  rewrite mulrCA big_split //=; congr (_ * (_ * _)).
  by apply: eq_bigr => x _; rewrite mxE.
case/injectivePn: Uf => i1 [i2 Di12 Ef12].
by rewrite (alternate_determinant Di12) ?simp //= => j; rewrite !mxE Ef12.
Qed.

Definition lift_perm_fun n i j (s : 'S_n) k :=
  if @unlift n.+1 i k is Some k' then @lift n.+1 j (s k') else j.

Lemma lift_permK : forall n i j s,
  cancel (@lift_perm_fun n i j s) (lift_perm_fun j i s^-1%g).
Proof.
move=> n i j s k; rewrite /lift_perm_fun.
by case: (unliftP i k) => [j'|] ->; rewrite (liftK, unlift_none) ?permK.
Qed.

Definition lift_perm n i j s := perm (can_inj (@lift_permK n i j s)).

Lemma lift_perm_id : forall n i j s, lift_perm i j s i = j :> 'I_n.+1.
Proof. by move=> n i j s; rewrite permE /lift_perm_fun unlift_none. Qed.

Lemma lift_perm_lift : forall n i j s k,
  lift_perm i j s (lift i k) = lift j (s k) :> 'I_n.+1.
Proof. by move=> n i j s k; rewrite permE /lift_perm_fun liftK. Qed.

Lemma lift_permM : forall n i j k s t,
  (@lift_perm n i j s * lift_perm j k t)%g = lift_perm i k (s * t)%g.
Proof.
move=> n i j k s t; apply/permP=> i1; case: (unliftP i i1) => [i2|] ->{i1}.
  by rewrite !(permM, lift_perm_lift).
by rewrite permM !lift_perm_id.
Qed.

Lemma lift_perm1 : forall n i, @lift_perm n i i 1 = 1%g.
Proof.
by move=> n i; apply: (mulgI (lift_perm i i 1)); rewrite lift_permM !mulg1.
Qed.

Lemma lift_permV : forall n i j s,
  (@lift_perm n i j s)^-1%g = lift_perm j i s^-1.
Proof.
by move=> n i j s; apply/eqP; rewrite eq_invg_mul lift_permM mulgV lift_perm1.
Qed.

Lemma odd_lift_perm : forall n i j s,
  @lift_perm n i j s = odd i (+) odd j (+) s :> bool.
Proof.
move=> n i j s; rewrite -{1}(mul1g s) -(lift_permM _ j) odd_permM.
congr (_ (+) _); last first.
  case: (prod_tpermP s) => ts ->{s} _.
  elim: ts => [|t ts IHts] /=; first by rewrite big_nil lift_perm1 !odd_perm1.
  rewrite big_cons odd_mul_tperm -(lift_permM _ j) odd_permM {}IHts //.
  congr (_ (+) _); rewrite (_ : _ j _ = tperm (lift j t.1) (lift j t.2)).
    by rewrite odd_tperm (inj_eq (@lift_inj _ _)).
  apply/permP=> k; case: (unliftP j k) => [k'|] ->.
    rewrite lift_perm_lift inj_tperm //; exact: lift_inj.
  by rewrite lift_perm_id tpermD // eq_sym neq_lift.
suff{i j s} odd_lift0: forall k : 'I_n.+1, lift_perm 0 k 1 = odd k :> bool.
  rewrite -!odd_lift0 -{2}invg1 -lift_permV odd_permV -odd_permM.
  by rewrite lift_permM mulg1.
move=> k; elim: {k}(k : nat) {1 3}k (erefl (k : nat)) => [|m IHm] k def_k.
  rewrite (_ : k = 0) ?lift_perm1 ?odd_perm1 //; exact: val_inj.
have le_mn: m < n.+1 by [rewrite -def_k ltnW]; pose j := Ordinal le_mn.
rewrite -(mulg1 1)%g -(lift_permM _ j) odd_permM {}IHm // addbC.
rewrite (_ : _ k _ = tperm j k).
  by rewrite odd_tperm neq_ltn def_k leqnn.
apply/permP=> i; case: (unliftP j i) => [i'|] ->; last first.
  by rewrite lift_perm_id tpermL.
apply: ord_inj; rewrite lift_perm_lift !permE /= eq_sym -if_neg neq_lift.
rewrite fun_if -val_eqE /= def_k /bump ltn_neqAle andbC.
case: leqP => [_ | lt_i'm] /=; last by rewrite -if_neg neq_ltn leqW.
by rewrite add1n eqSS eq_sym; case: eqP.
Qed.

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
rewrite -trmx_row' -trmx_col' det_trmx; congr (\det _).
by apply/matrixP=> ? ?; rewrite !mxE.
Qed.

Lemma expand_det_col : forall n (A : 'M_n) j0,
  \det A = \sum_i (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -det_trmx (expand_det_row _ j0).
by apply: eq_bigr => i _; rewrite cofactor_tr mxE.
Qed.

Lemma mulmx_adjr : forall n (A : 'M_n), A *m adjugate A = (\det A)%:M.
Proof.
move=> n A; apply/matrixP=> i1 i2; rewrite !mxE; case Di: (i1 == i2).
  rewrite (eqP Di) (expand_det_row _ i2) //=.
  by apply: eq_bigr => j _; congr (_ * _); rewrite mxE.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= !mxE Di eq_refl.
rewrite -{2}(alternate_determinant (negbT Di) EBi12).
rewrite (expand_det_row _ i2); apply: eq_bigr => j _.
rewrite !mxE eq_refl; congr (_ * (_ * _)).
apply: eq_bigr => s _; congr (_ * _); apply: eq_bigr => i _.
by rewrite !mxE eq_sym -if_neg neq_lift.
Qed.

Lemma trmx_adj : forall n (A : 'M_n), (adjugate A)^T = adjugate A^T.
Proof. by move=> n A; apply/matrixP=> i j; rewrite !mxE cofactor_tr. Qed.

Lemma mulmx_adjl : forall n (A : 'M_n), adjugate A *m A = (\det A)%:M.
Proof.
move=> n A; apply: trmx_inj; rewrite trmx_mul trmx_adj mulmx_adjr.
by rewrite det_trmx trmx_scalar.
Qed.

Lemma detM : forall (n : pos_nat) (A B : 'M_n), \det (A * B) = \det A * \det B.
Proof. move=> n; exact: det_mulmx. Qed.

Lemma mx11_scalar : forall A : matrix R 1 1, A = (A 0 0)%:M.
Proof. by move=> A; apply/matrixP=> i j; rewrite [i]ord1 [j]ord1 mxE eqxx. Qed.

Lemma det_scalar : forall n a, \det (a%:M : 'M_n) = a ^+ n.
Proof.
move=> n a; rewrite -{1}(mulr1 a) scalar_mx_mul mulmx_scalar det_scalemx.
by rewrite det1 simp.
Qed.

Lemma det_scalar1 : forall a, \det (a%:M : 'M_1) = a.
Proof. exact: det_scalar. Qed.

Lemma det_perm_mx_neq0 : forall n s, \det (@perm_mx R n s) != 0. 
Proof.
move=> n s; rewrite det_perm_mx.
by case: (s : bool); rewrite ?oppr_eq0 nonzero1r.
Qed.

Lemma det_ublock : forall n1 n2 Aul Aur Alr,
  \det (block_mx Aul Aur 0 Alr : 'M_(n1 + n2)) = \det Aul * \det Alr.
Proof.
move=> n1 n2 Aul Aur Alr; elim: n1 => [|n1 IHn1] in Aul Aur *.
  have ->: Aul = 1%:M by apply/matrixP=> i [].
  rewrite det1 mul1r; congr (\det _); apply/matrixP=> i j.
  by do 2![rewrite !mxE; case: splitP => [[]|k] //=; move/val_inj=> <- {k}].
rewrite (expand_det_col _ (lshift n2 0)) big_split_ord /=.
rewrite addrC big1 1?simp => [|i _]; last by rewrite block_mxEll mxE simp.
rewrite (expand_det_col _ 0) big_distrl /=; apply eq_bigr=> i _.
rewrite block_mxEul -!mulrA; do 2!congr (_ * _).
rewrite -trmx_row' mx_row'_paste -!trmx_col' !mx_col'_lshift -!trmx_row'.
by rewrite !mx_row'_paste mx_col'0 IHn1.
Qed.

Lemma det_lblock :  forall n1 n2 Aul All Alr,
  \det (block_mx Aul 0 All Alr : 'M_(n1 + n2)) = \det Aul * \det Alr.
Proof.
move=> n1 n2 Aul All Alr.
by rewrite -det_trmx trmx_block trmx0 det_ublock !det_trmx.
Qed.

End ComMatrix.

Notation "\det A" := (determinant A) : ring_scope.
Notation "\adj A" := (adjugate A) : ring_scope.

Section MatrixInv.

Variables (R : comUnitRingType) (n : pos_nat).

Definition unit_mx : pred 'M_n := fun A => GRing.unit (\det A : R).
Definition invmx A := if unit_mx A then (\det A)^-1 *m: \adj A else A.

Lemma mulVmx : {in unit_mx, left_inverse 1 invmx *%R}.
Proof.
move=> A; rewrite -topredE /= => nsA; rewrite /invmx nsA.
by rewrite -mulmxE -scalemxAl mulmx_adjl -mulmx_scalar -scalar_mx_mul mulVr.
Qed.

Lemma mulmxV : {in unit_mx, right_inverse 1 invmx *%R}.
Proof.
move=> A; rewrite -topredE /= => nsA; rewrite /invmx nsA.
by rewrite -mulmxE -scalemxAr mulmx_adjr -mulmx_scalar -scalar_mx_mul mulVr.
Qed.

Lemma intro_unit_mx : forall A B : 'M_n, B * A = 1 /\ A * B = 1 -> unit_mx A.
Proof.
move=> A B [BA1 AB1]; apply/unitrP; exists (\det B).
by rewrite -!detM BA1 AB1 det1.
Qed.

Lemma invmx_out : {in predC unit_mx, invmx =1 id}.
Proof. by move=> A; rewrite inE /= /invmx -if_neg => ->. Qed.

Definition matrix_unitRingMixin :=
  UnitRingMixin mulVmx mulmxV intro_unit_mx invmx_out.
Canonical Structure matrix_unitRing :=
  Eval hnf in UnitRingType matrix_unitRingMixin.

Lemma det_invmx : forall A : 'M_n, \det A^-1 = (\det A)^-1.
Proof.
move=> A; case/orP: (orbN (GRing.unit A)) => U_A; last by rewrite !invr_out.
by apply: (@mulrI R (\det A) U_A); rewrite -detM !divrr // det1.
Qed.

Lemma trmx_unit : forall A : 'M_n, GRing.unit A^T = GRing.unit A.
Proof. by move=> A; rewrite /GRing.unit /= /unit_mx det_trmx. Qed.

Lemma trmx_inv : forall A : 'M_n, A^-1^T = (A^T)^-1.
Proof.
move=> A; rewrite /GRing.inv /= /invmx /unit_mx det_trmx.
by rewrite -trmx_adj -trmx_scale (fun_if (fun B => B^T)).
Qed.

Lemma perm_mxV : forall s : 'S_n, perm_mx R s^-1%g = (perm_mx R s)^-1.
Proof.
move=> s; set A' := perm_mx _ _.
rewrite -[_^-1]mul1r; apply: (canRL (mulrK _)).
  by apply/unitrP; exists A'; rewrite -!mulmxE !mulmx_perm ?gsimp ?perm_mx1.
by rewrite -!mulmxE !mulmx_perm ?gsimp ?perm_mx1.
Qed.

End MatrixInv.

