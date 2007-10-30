Require Import ssreflect ssrbool funs eqtype ssrnat seq paths fintype tuple.
Require Import ssralg ssrbig div groups matrix ssrpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Ring.
Import Monoid.Equations.

Open Scope ring_scope.

Section Cayley.

Variable R : commutative_.

Variable n : pos_nat.

Notation Local nn := (pos_nat_val n) (only parsing).
Notation Local "'R'" := R
  (at level 0, format "'R'").
Notation Local "'R' [ 'X' ]" := (polynomial R)
  (at level 0, format "'R' [ 'X' ]").
Notation Local "'M' ( 'R' )" := (matrix R nn nn)
  (at level 0, format "'M' ( 'R' )").
Notation Local "'M' ( 'R' [ 'X' ] )" :=
  (matrix (poly_commutative_ring R) nn nn)
  (at level 0, format "'M' ( 'R' [ 'X' ] )").
Notation Local "'M' ( 'R' ) [ 'X' ]" := (polynomial (matrix_ring R n))
  (at level 0, format "'M' ( 'R' ) [ 'X' ]").

(* Defining the characteristic polynomial *)

Definition matrixC (A : M(R)) : M(R[X]) := \matrix_(i, j) \C (A i j).

Definition char_poly (A : M(R)) : R[X] := \det (\Z \X - matrixC A).

(* The isomorhism phi : M(R[X]) <-> M(R)[X] *)

Definition phi (A : M(R[X])) : M(R)[X] :=
  \poly_(k < \max_(i) \max_(j) size (A i j)) \matrix_(i, j) coef (A i j) k.

Lemma coef_phi : forall A i j k, coef (phi A) k i j = coef (A i j) k.
Proof.
move=> A i j k; rewrite /phi; rewrite coef_poly_of.
case: (ltnP k _) => le_m_k; rewrite mxK // [coef _ _]sub_default //.
apply: leq_trans (leq_trans (leq_bigmax i) le_m_k); exact: (leq_bigmax j).
Qed.

Lemma phi_polyC : forall A, phi (matrixC A) = \C A.
Proof.
move=> A; apply/coef_eqP=> k; apply/matrixP=> i j.
by rewrite coef_phi !mxK !coef_polyC; case k; last rewrite mxK.
Qed.

Lemma phi_zero : phi 0 = 0.
Proof.
apply/coef_eqP=> k; apply/matrixP=> i j.
by rewrite coef_phi mxK !coef0 mxK.
Qed.

Lemma phi_add : forall (A1 A2 : M(R[X])), phi (A1 + A2) = (phi A1) + (phi A2).
Proof.
move=> A1 A2; apply/coef_eqP => k; apply/matrixP=> i j.
by rewrite coef_phi !mxK !coef_add_poly mxK !coef_phi.
Qed.

Lemma phi_opp : forall A, phi (- A) = - phi A.
Proof.
move=> A; apply/coef_eqP=> k; apply/matrixP=> i j.
by rewrite coef_phi mxK coef_opp mxK !mulN1r coef_phi coef_opp. 
Qed.

Lemma phi_one : phi 1 = 1.
Proof.
apply/coef_eqP=> k; apply/matrixP=> i j.
rewrite coef_phi mxK (fun_if (fun p => coef p k)) coef0 !coef_polyC.
by case: k => [|k]; rewrite /= !mxK // if_same.
Qed.

Lemma phi_mul : forall (A1 A2 : M(R[X])), phi (A1 * A2) = (phi A1) * (phi A2).
Proof.
move=> A1 A2; apply/coef_eqP=> k; apply/matrixP=> i j.
rewrite !coef_phi !mxK !coef_mul_poly mxK_sum coef_sum.
pose F k1 k2 := coef (A1 i k1) k2 * coef (A2 k1 j) (k - k2).
transitivity (\sum_(k1) \sum_(k2 <= k) F k1 k2); rewrite {}/F.
  by apply: eq_bigr=> k1 _; rewrite coef_mul_poly.
rewrite exchange_big /=; apply: eq_bigr=> k2 _.
by rewrite mxK; apply: eq_bigr=> k1 _; rewrite !coef_phi.
Qed.

(* Evaluating a polynomial on matrices *)

Definition Zpoly (p : R[X]) : M(R)[X] := \poly_(i < size p) \Z (coef p i).

Lemma coef_Zpoly : forall p k, coef (Zpoly p) k = \Z (coef p k).
Proof.
move=> p k; rewrite coef_poly_of; case: (ltnP k _) => // le_p_k.
by rewrite coef_default // scalarmx0.
Qed.

Lemma ZpolyX : Zpoly \X = \X.
Proof.
apply/coef_eqP=> k; apply/matrixP=> i j; rewrite coef_Zpoly !coef_polyX.
by case: (k == _); rewrite !mxK ?if_same.
Qed.

Lemma phi_Zpoly : forall p, phi (\Z p) = Zpoly p.
Proof.
move=> p; apply/coef_eqP=> k; apply/matrixP=> i j.
by rewrite coef_phi coef_Zpoly !mxK; case: (i == j); rewrite ?coef0.
Qed.

(* The theorem in three lines! *)

Theorem Cayley_Hamilton : forall A, (Zpoly (char_poly A)).[A] = 0.
Proof.
move=> A; apply/eqP; apply/factor_theorem.
rewrite -phi_Zpoly -mulmx_adjl phi_mul; move: (phi _) => q; exists q.
by rewrite phi_add phi_opp phi_Zpoly phi_polyC ZpolyX.
Qed.

End Cayley.
