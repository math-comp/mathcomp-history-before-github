(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import bigops ssralg matrix poly.

(*****************************************************************************)
(* This file contains the definitions of:                                    *)
(*  - char_poly A  : Characteristic polynomial of A                          *)
(*  - phi : the isomorphism between the rings  M(R[X]) and M(R)[X]           *)
(*    with R a commutative and                                               *)
(*     M(R[X]) : matrices with coefficients in the polynomial ring of R      *)
(*     M(R)[X] : polynomials with coefficients in the matrix ring of R       *)
(*  - Zpoly : the injection from the polynomial ring to M(R)[X]              *)
(* In addition to the lemmas relevant to these definitions, this file also   *)
(* contains a proof of the Cayley-Hamilton Theorem.                          *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Import Monoid.Theory.

Open Local Scope ring_scope.

Section Cayley.

Variable R : comRingType.

Variable n : pos_nat.

Notation Local nn := (pos_nat_val n) (only parsing).
Notation Local "'R'" := R
  (at level 0, format "'R'").
Notation Local "'R' [ 'X' ]" := {poly R}
  (at level 0, format "'R' [ 'X' ]").
Notation Local "'M' ( 'R' )" := (matrix R nn nn)
  (at level 0, format "'M' ( 'R' )").
Notation Local "'M' ( 'R' [ 'X' ] )" :=
  (matrix (poly_ringType R) nn nn)
  (at level 0, format "'M' ( 'R' [ 'X' ] )").
Notation Local "'M' ( 'R' ) [ 'X' ]" := {poly (matrix R n n)}
  (at level 0, format "'M' ( 'R' ) [ 'X' ]").

(* The characteristic polynomial *)
Open Scope matrix_scope.
Definition matrixC (A : M(R)) : M(R[X]) := \matrix_(i, j) (A i j)%:P.

Definition char_poly (A : M(R)) : R[X] := \det ('X%:M - matrixC A).

(* The isomorhism phi : M(R[X]) <-> M(R)[X] *)

Definition phi (A : M(R[X])) : M(R)[X] :=
  \poly_(k < \max_i \max_j size (A i j)) \matrix_(i, j) (A i j)`_k.

Lemma coef_phi : forall A i j k, (phi A)`_k i j = (A i j)`_k.
Proof.
move=> A i j k; rewrite coef_poly.
case: (ltnP k _) => le_m_k; rewrite mxE // nth_default //.
apply: leq_trans (leq_trans (leq_bigmax i) le_m_k); exact: (leq_bigmax j).
Qed.

Lemma phi_polyC : forall A, phi (matrixC A) = A%:P.
Proof.
move=> A; apply/polyP=> k; apply/matrixP=> i j.
by rewrite coef_phi !mxE !coefC; case k; last rewrite /= mxE.
Qed.

Lemma phi_zero : phi 0 = 0.
Proof.
apply/polyP=> k; apply/matrixP=> i j.
by rewrite coef_phi mxE !coef0 mxE.
Qed.

Lemma phi_add : forall (A1 A2 : M(R[X])), phi (A1 + A2) = (phi A1) + (phi A2).
Proof.
move=> A1 A2; apply/polyP => k; apply/matrixP=> i j.
by rewrite coef_phi !mxE !coef_add_poly mxE !coef_phi.
Qed.

Lemma phi_opp : forall A, phi (- A) = - phi A.
Proof.
move=> A; apply/polyP=> k; apply/matrixP=> i j.
by rewrite coef_phi mxE coef_opp mxE coef_phi coef_opp.
Qed.

Lemma phi_one : phi 1 = 1.
Proof.
apply/polyP=> k; apply/matrixP=> i j.
rewrite coef_phi mxE (fun_if (fun p : {poly _} => p`_k)) coef0 !coefC.
by case: k => [|k]; rewrite /= !mxE // if_same.
Qed.

Lemma phi_mul : forall (A1 A2 : M(R[X])), phi (A1 * A2) = (phi A1) * (phi A2).
Proof.
move=> A1 A2; apply/polyP=> k; apply/matrixP=> i j.
rewrite !coef_phi !mxE !coef_mul summxE coef_sum.
pose F k1 k2 := (A1 i k1)`_k2 * (A2 k1 j)`_(k - k2).
transitivity (\sum_k1 \sum_(k2 < k.+1) F k1 k2); rewrite {}/F.
  by apply: eq_bigr=> k1 _; rewrite coef_mul.
rewrite exchange_big /=; apply: eq_bigr=> k2 _.
by rewrite mxE; apply: eq_bigr=> k1 _; rewrite !coef_phi.
Qed.

(* Writing a polynomial as a polynomial on matrices *)

Definition Zpoly (p : R[X]) : M(R)[X] := \poly_(i < size p) (p`_i)%:M.

Lemma coef_Zpoly : forall p k, (Zpoly p)`_k = (p`_k)%:M.
Proof.
move=> p k; rewrite coef_poly; case: (ltnP k _) => // le_p_k.
by rewrite nth_default // scalar_mx0.
Qed.

Lemma ZpolyX : Zpoly 'X = 'X.
Proof.
apply/polyP=> k; apply/matrixP=> i j; rewrite coef_Zpoly !coefX.
by case: (k == _); rewrite !mxE ?if_same.
Qed.

Lemma phi_Zpoly : forall p, phi p%:M = Zpoly p.
Proof.
move=> p; apply/polyP=> k; apply/matrixP=> i j.
by rewrite coef_phi coef_Zpoly !mxE; case: (i == j); rewrite ?coef0.
Qed.

(* The theorem in three lines! *)

Theorem Cayley_Hamilton : forall A, (Zpoly (char_poly A)).[A] = 0.
Proof.
move=> A; apply/eqP; apply/factor_theorem.
rewrite -phi_Zpoly -mulmx_adjl phi_mul; move: (phi _) => q; exists q.
by rewrite phi_add phi_opp phi_Zpoly phi_polyC ZpolyX.
Qed.

End Cayley.
