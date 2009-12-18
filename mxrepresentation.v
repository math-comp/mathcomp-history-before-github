Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import choice fintype finfun bigops prime binomial ssralg poly finset.
Require Import groups morphisms automorphism normal perm finalg action gprod.
Require Import zmodp matrix commutators cyclic center pgroups sylow maximal.

(****************************************************************************)
(*  This file provides linkage between classic Group Theory and commutative *)
(* algebra -- representation theory. Since general abstract linear algebra  *)
(* is still being sorted out, we develop the required theory here on the    *)
(* assumption that all vector spaces are matrix spaces, indeed that most    *)
(* are row matrix spaces; our representation theory is specialized to the   *)
(* latter case. We provide some boilerplate for this mock linear algebra    *)
(* (conversions between row and rectangular matrices, from linear functions *)
(* to matrices), some basic definitions and results of representation       *)
(* theory: matrix ring centralizer, minimal polynomial, representation,     *)
(* enveloping algebra, reducible, irreducible and absolutely irreducible    *)
(* representation, representation kernels, the Schur lemma, Maeshke's       *)
(* theorem, the Jacobson Density theorem, the construction of a splitting   *)
(* field of an irreducible representation, and of reduced, tensored, and    *)
(* factored representations. We also define a representation corresponding  *)
(* to the acion of a group on an elementary abelian p-group.                *)
(*   The operations defined here include:                                   *)
(*      mxvec A == a row vector of width m * n holding all the entries of   *)
(*                 the m x n matrix A.                                      *)
(*     vec_mx v == the inverse of mxvec, reshaping a vector of width m * n  *)
(*                 back into into an m x n rectangular matrix.              *)
(*    linear f <=> f : 'M_(m1, n1) -> 'M_(m2, n2) is a linear mapping       *)
(*   linear_fun == a Structure that encapsulates the linear properties; we  *)
(*                 define such a structure for all the matrix operations    *)
(*                 that are relevant here: row, ^T, mxvec, vec_mx, *m:, -,  *)
(*                 and *m on the left (mulmx) and right (mulmxr). The       *)
(*                 strucures also recognize unary (\o) and binary (add_lin, *)
(*                 via addition) composition of linear functions, as well   *)
(*                 as the identity (idfun) and zero (null_lin) functions.   *)
(*    lin1_mx f == the m x n matrix that emulates via right product         *)
(*                 a (linear) function f : 'rV_m -> 'rV_n on ROW VECTORS    *)
(*     lin_mx f == the (m1 * n1) x (m2 * n2) matrix that emulates, via the  *)
(*                 right multiplication on the mxvec encodings, a linear    *)
(*                 function f : 'M_(m1, n1) -> 'M_(m2, n2)                  *)
(* is_scalar_mx A == A is a scalar matrix (A = a%:M for some A)             *)
(*    cent_mx E == an n ^ 2 x n ^ 2 matrix whose row-space consists of the  *)
(*                 mxvec encodings of the centraliser of the algebra whose  *)
(*                 mxvec encodings form the row-space of E (which must thus *)
(*                 be an m x n ^ 2 matrix for some m).                      *)
(*     rVpoly v == the little-endian decoding of the row vector v as a      *)
(*                 polynomial p = \sum_i (v 0 i)%:P * 'X^i                  *)
(*    poly_rV p == the partial inverse to rVpoly, for polynomials of degree *)
(*                 less than d to 'rV_d (d is inferred from the context).   *)
(*  horner_mx A == the morphism from {poly R} to 'M_n (n of the form n'.+1) *)
(*                 mapping a (scalar) polynomial p to the value of its      *)
(*                 scalar matrix interpretation at A (this is an instance   *)
(*                 of the generic horner_morph construct defined in poly).  *)
(* minpoly_mx A d == the d x n ^ 2 matrix whose rows are the mxvec encoding *)
(*                 of the increasing powers of A. We thus have              *)
(*                 vec_mx (v *m minpoly_mx A d) = horner_mx A (rVpoly v).   *)
(* degree_mxminpoly A == the (positive) degree of the minimal polynomial of *)
(*                 the matrix A (degree_mxminpoly A = 1 iff A is scalar).   *)
(*  mxminpoly A == the minimal polynomial of A, i.e., the smallest monic    *)
(*                 polynomial that anihilates A.                            *)
(* mx_inv_horner A == the inverse of horner_mx A for polynomials of degree  *)
(*                 smaller than degree_mxminpoly A.                         *)
(* mx_representation F G n == the Structure type for representations of G   *)
(*                 with n x n matrices with coefficients in F. Note that    *)
(*                 rG : mx_representation F G n coerces to a function from  *)
(*                 the element type of G to 'M_n, and conversely all such   *)
(*                 functions have a Canonical mx_representation.            *)
(*  mx_repr G r == r : gT -> 'M_n defines a (matrix) group representation   *)
(*                 on G : {set gT}.                                         *)
(* enveloping_algebra_mx rG == a #|subg_of G| x n ^ 2 matrix whose rows     *)
(*                 are the mxvec encodings of the image of G under rG, and  *)
(*                 whose row space therefore encodes the enveloping algebra *)
(*                 of the representation of G.                              *)
(*   rfix_mx rG == an n x n matrix whose row space is the set of vectors    *)
(*                 fixed (centralised) by the representation of G by r.     *)
(*   rcent rG A == the subgroup of G whose representation via r commutes    *)
(*                 with the square matrix A.                                *)
(*   rstab rG U == the subgroup of G whose representation via r fixes all   *)
(*                 vectors in U, pointwise.                                 *)
(*  rstabs rG U == the subgroup of G whose representation via r fixes the   *)
(*                 row subspace of U globally.                              *)
(* submodmx rG U == the row-space of the n x n matrix U is a submodule      *)
(*                 (globally invariant) under the representation rG of G.   *)
(* submod_repr Umod == a representation of G on 'rV_(\rank U) equivalent to *)
(*                 the restriction of rG to U (here Umod : submodmx rG U).  *)
(* val/in_submod rG U == the projections resp. from/onto 'rV_(\rank U),     *)
(*                 that correspond to submod_repr r G U (these work both on *)
(*                 vectors and row spaces).                                 *)
(* factmod_repr Umod == a representation of G on 'rV_(\rank (cokermx U))    *)
(*                 that is equivalent to the factor module 'rV_n / U        *)
(*                 induced by U and rG (here Umod : submodmx rG U).         *)
(* val/in_factmod rG U == the projections for factmod_repr r G U.           *)
(* mx_reducible rG == the representation r of G is reducible: it is either  *)
(*                 trivial, or it has a non-trivial proper submodule.       *)
(* mx_irrreducible rG == the representation r of G is not reducible; as it  *)
(*                 is not possible to decide reducibility in general, this  *)
(*                 is a negation in Prop.                                   *)
(* MatrixFormula.redmx_sat rG == the representation of G via rG is          *)
(*                 reducible; this is a bool expression, which requires a   *)
(*                 decField structure. The MatrixFormula module, described  *)
(*                 below, is a general toolkit for building formal          *)
(*                 expressions involving matrices.                          *)
(*   mxcentg rG A == A commutes with every matrix in the rpresentation of G *)
(*                 and thus with every matrix in its enveloping algebra.    *)
(*      rker rG == the kernel of the representation of r on G, i.e., the    *)
(*                 subgroup of elements of G mapped to the identity by rG.  *)
(* mx_repr_faithful rG == the representation rG of G is faithful (its       *)
(*                 kernel is trivial).                                      *)
(* mx_absolutely_irreducible rG == the representation rG of G is absolutely *)
(*                 irreducible: its enveloping algebra is the full matrix   *)
(*                 ring. (This is classically equivalent to ``rG does not   *)
(*                 reduce in any field extension'', a result which only     *)
(*                 holds under double negation, intuitionistically.)        *)
(* subg_repr rG sHG == the restriction to H of the representation rG of G;  *)
(*                 here sHG : H \subset G.                                  *)
(* comp_repr f rG == the representation of f @*^-1 G obtained by composing  *)
(*                 a morphism f with rG.                                    *)
(* rconj_repr rG uB == the conjugate representation mapping x to            *)
(*                 B * rG x * B^-1; here uB : B \in unitmx.                 *)
(* quo_repr sHK nHG == the representation of G / H induced by rG, given     *)
(*                 sHK : H \subset rker rG, and nHG : G \subset 'N(H).      *)
(* kquo_repr rG == the representation induced on G / rker rG by rG.         *)
(* map_repr fRM rG == the representation f \o rG, whose module is the       *)
(*                 tensor product of the module of rG with the extension    *)
(*                 field into which f embeds the base field of rG; here     *)
(*                 fRM : GRing.morphism f.                                  *)
(* The next constructions assume that F is a finite field.                  *)
(*        'Zm%act == the action of {unit F} on 'M[F]_(m, n)                 *)
(*         rowg A == the additive group of 'rV[F]_n spanned by the row      *)
(*                   space of the matrix A.                                 *)
(*      rowg_mx L == the partial inverse to rowg, for 'Zm-stable groups L   *)
(*                   of 'rV[F]_n we have rowg (rowg_mx L) = L.              *)
(*     GLrepr F n == the natural, faithful representation of 'GL_n[F].      *)
(*     reprGLm rG == the morphism G >-> 'GL_n[F] equivalent to the          *)
(*                 representation r of G (with rG : mx_repr r G).           *)
(*   ('MR rG)%act == the action of G on 'rV[F]_n equivalent to the          *)
(*                 representation r of G (with rG : mx_repr r G).           *)
(* The last set of constructions define the interpretation of a normal      *)
(* non-trivial elementary abelian p-subgroup as an 'F_p module. We assume   *)
(* abelE : p.-abelem E and ntE : E != 1, throughout, as these are needed to *)
(* build the isomorphism between E and a nontrivial 'rV['F_p]_n.            *)
(*         'rV(E) == the type of row vectors of the 'F_p module equivalent  *)
(*                   to E when E is a non-trivial p.-abelem group.          *)
(*          'M(E) == the corresponding type of matrices.                    *)
(*         'dim E == the width of vectors/matrices in 'rV(E) / 'M(E)        *)
(* abelem_rV abelE ntE == the 1-to-1 injection of E onto 'rV(E)             *)
(*  rVabelem abelE ntE == the 1-to-1 projection of 'rV(E) onto E            *)
(* abelem_repr abelE ntE nEG == the representation of G on 'rV(E) that is   *)
(*                 equivalent to conjugation by G in E; here abelE, ntE are *)
(*                 as above, and G \subset 'N(E).                           *)
(*     In addition, more involved constructions are encapsulated in two     *)
(* submodules:                                                              *)
(* MatrixGenField == a module that encapsulates the lengthy details of the  *)
(*                 construction of appropriate extension fields. We assume  *)
(*                 we have an irreducible representation r of a group G,    *)
(*                 and a non-scalar matrix A that centralises an r(G), as   *)
(*                 this data is readily extracted from the Jacobson Density *)
(*                 Theorem. It then follows from Schur's Lemma that the     *)
(*                 ring generated by A is a field on which the extension of *)
(*                 the representation r of G is reducible. Note that this   *)
(*                 is equivalent to the more traditional quotient of the    *)
(*                 polynomial ring by an irreducible polynomial (namely the *)
(*                 minimal polynomial of A), but much better suited for our *)
(*                 needs.                                                   *)
(*   Here are the main definitions of MatrixGenField; they all take as      *)
(* argument three proofs: rG : mx_repr r G, irrG : mx_irreducible rG, and   *)
(* cGA : mxcentg rG A, which ensure the validity of the construction and    *)
(* allow us to define Canonical Structures (~~ is_scalar_mx A is only       *)
(* needed to prove reducibility).                                           *)
(*  + gen_of irrG cGA == the carrier type of the field generated by A. It   *)
(*                 is at least equipped with a fieldType structure; we also *)
(*                 propagate any decFieldType/finFieldType structures on    *)
(*                 the original field.                                      *)
(*  + gen irrG cGA == the morphism injecting into gen_of rG irrG cGA        *)
(*  + groot irrG cGA == the root of mxminpoly A in the gen_of field         *)
(*  + gen_repr irrG cGA == an alternative to the field extension            *)
(*                 representation, which consists in reconsidering the      *)
(*                 original module as a module over the new gen_of field,   *)
(*                 thereby DIVIDING the original dimension n by the degree  *)
(*                 of the minimal polynomial of A. This can be simpler than *)
(*                 the extension method, and is actually required by the    *)
(*                 proof that odd groups are p-stable (B & G 6.1-2, and     *)
(*                 Appendix A), but is only applicable if G is the LARGEST  *)
(*                 group represented by rG (e.g., NOT for B & G 2.6).       *)
(*  + val_gen/in_gen rG irrG cGA : the bijections from/to the module        *)
(*                 corresponding to gen_repr.                               *)
(*  + rowval_gen rG irrG cGA : the projection of row spaces in the module   *)
(*                 corresponding to gen_repr to row spaces in 'rV_n.        *)
(* MatrixFormula == a toolkit for building formal matrix expressions        *)
(*  + eval_mx e == GRing.eval lifted to matrices (== map_mx (GRing.eval e)) *)
(*  + mx_term A == GRing.Const lifted to matrices.                          *)
(*  + mulmx_term A B == the formal product of two matrices of terms         *)
(*  + mxrank_form m A == a GRing.formula asserting that the interpretation  *)
(*                 of the term matrix A has rank m.                         *)
(*  + subsetmx_form A B == a GRing.formula asserting that the row space of  *)
(*                 the interpretation of the term matrix A is included in   *)
(*                 the row space of the interpretation of B.                *)
(*  + submodmx_form r G U == a formula asserting that the interpretation of *)
(*                 U is a submodule of the representation of G via r.       *)
(*  + redmx_form r G == a formula asserting that the representation of G    *)
(*                 via r is reducible (r is a manifest constant).           *)
(*  + seq_of_rV v == the seq corresponding to a row vector.                 *)
(*  + row_env e == the flattening of a tensored environment e : seq 'rV_d   *)
(*  + row_var d k == the term vector of width d such that for e : seq 'rV_d *)
(*                 we have eval e 'X_k = eval_mx (row_env e) (row_var d k). *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* Bijections mxvec : 'M_(m, n) <----> 'rV_(m * n) : vec_mx *)
Section VecMatrix.

Variables (R : Type) (m n : nat).

Lemma mxvec_cast : #|{:'I_m * 'I_n}| = (m * n)%N. 
Proof. by rewrite card_prod !card_ord. Qed.

Definition mxvec_index (i : 'I_m) (j : 'I_n) :=
  cast_ord mxvec_cast (enum_rank (i, j)).

CoInductive is_mxvec_index : 'I_(m * n) -> Type :=
  IsMxvecIndex i j : is_mxvec_index (mxvec_index i j).

Lemma mxvec_indexP : forall k, is_mxvec_index k.
Proof.
move=> k; rewrite -[k](cast_ordK (esym mxvec_cast)) esymK.
by rewrite -[_ k]enum_valK; case: (enum_val _).
Qed.

Coercion pair_of_mxvec_index k (i_k : is_mxvec_index k) :=
  let: IsMxvecIndex i j := i_k in (i, j).

Definition mxvec (A : 'M[R]_(m, n)) :=
  castmx (erefl _, mxvec_cast) (\row_k A (enum_val k).1 (enum_val k).2).

Definition vec_mx (u : 'rV[R]_(m * n)) := \matrix_(i, j) u 0 (mxvec_index i j).

Lemma mxvecE : forall A i j, mxvec A 0 (mxvec_index i j) = A i j.
Proof. by move=> A i j; rewrite castmxE mxE cast_ordK enum_rankK. Qed.

Lemma mxvecK : cancel mxvec vec_mx.
Proof. by move=> A; apply/matrixP=> i j; rewrite mxE mxvecE. Qed.

Lemma vec_mxK : cancel vec_mx mxvec.
Proof.
by move=> u; apply/rowP=> k; case/mxvec_indexP: k => i j; rewrite mxvecE mxE.
Qed.

End VecMatrix.

Prenex Implicits mxvec vec_mx mxvec_indexP mxvecK vec_mxK scalemx.

(* A generic interface for linear matrix-to-matrix functions. *)
Section Linear.

Variables R : ringType.

Section OneLinear.

Variables m1 n1 m2 n2 : nat.
Local Notation f12 := ('M[R]_(m1, n1) -> 'M[R]_(m2, n2)).

Definition linear (f : f12) := forall a, {morph f : u v / a *m: u + v}.
Structure linear_fun := LinearFun {linear_fval :> f12; _ : linear linear_fval}.

Definition clone_linear (f g : f12) lT & phant_id (linear_fval lT) g :=
  fun fL & phant_id (LinearFun fL) lT => @LinearFun f fL.

Variable f : linear_fun.

Lemma linearP : linear f. Proof. by case f. Qed.

Lemma linear0 : f 0 = 0.
Proof. by rewrite -(addNr 0) -scaleN1mx linearP scaleN1mx addNr. Qed.

Lemma linearD : {morph f : u v / u + v}.
Proof. by move=> u v; rewrite -{1}[u]scale1mx linearP scale1mx. Qed.

Lemma linearZ : forall a, {morph f : u / a *m: u}.
Proof. by move=> a u; rewrite -[a *m: _]addr0 linearP linear0 addr0. Qed.

Lemma linearN : {morph f : u / - u}.
Proof. by move=> u /=; rewrite -!scaleN1mx linearZ. Qed.

Lemma linear_sub : {morph f : u v / u - v}.
Proof. by move=> u v /=; rewrite linearD linearN. Qed.

Lemma linear_sum : forall I r (P : pred I) F,
  f (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) f (F i).
Proof. exact: (big_morph f linearD linear0). Qed.

End OneLinear.

(* Canonical instances of linear_fun; we introduce a specific head *)
(* for binary operators (like *m) curried to the left.             *)
Section MoreLinear.

Variables m1 n1 m2 n2 m3 n3 : nat.
Local Notation f12 := ('M[R]_(m1, n1) -> 'M[R]_(m2, n2)).
Local Notation lf12 := (linear_fun m1 n1 m2 n2).
Local Notation lf23 := (linear_fun m2 n2 m3 n3).

Lemma idfun_linear_proof : @linear m1 n1 m1 n1 idfun. Proof. by []. Qed.
Canonical Structure idfun_linear := LinearFun idfun_linear_proof.

Lemma comp_linear_proof : forall (f : lf23) (g : lf12), linear (f \o g).
Proof. by move=> f g a u v; rewrite /= !linearP. Qed.
Canonical Structure comp_linear f g := LinearFun (comp_linear_proof f g).

Lemma trmx_linear_proof : @linear m1 n1 n1 m1 trmx.
Proof. by move=> a u v; rewrite /= trmx_add trmx_scale. Qed.
Canonical Structure trmx_linear := LinearFun trmx_linear_proof.

Definition null_lin_head t : f12 := fun _ => let: tt := t in 0.
Lemma null_linear_proof : linear (null_lin_head tt).
Proof. by move=> a u v; rewrite scalemx0 addr0. Qed.
Canonical Structure null_linear := LinearFun null_linear_proof.

Lemma opp_linear_proof : @linear m1 n1 m1 n1 -%R.
Proof. by move=> a u v; rewrite scalemxN oppr_add. Qed.
Canonical Structure opp_linear := LinearFun opp_linear_proof.

Definition add_lin_head t (f g : f12) u := let: tt := t in f u + g u.
Lemma add_linear_proof : forall f g : lf12, linear (add_lin_head tt f g).
Proof.
by move=> f g a u v; rewrite /= !linearP scalemx_addr addrCA -!addrA addrCA.
Qed.
Canonical Structure add_linear f g := LinearFun (add_linear_proof f g).

Definition mulmxr_head t (B : 'M[R]_(n1, n2)) (A : 'M_(m1, n1)) :=
  let: tt := t in A *m B.
Lemma mulmxr_linear_proof : forall B, linear (mulmxr_head tt B).
Proof. by move=> B a A1 A2; rewrite /= mulmx_addl scalemxAl. Qed.
Canonical Structure mulmxr_linear B := LinearFun (mulmxr_linear_proof B).

Lemma row_linear_proof : forall i, linear (row i : 'M[R]_(m1, n1) -> 'rV[R]_n1).
Proof. by move=> i a A B; apply/rowP=> j; rewrite !mxE. Qed.
Canonical Structure row_linear i := LinearFun (row_linear_proof i).

Lemma vec_mx_linear_proof : linear (@vec_mx R m1 n1).
Proof. by move=> a u v; apply/matrixP=> i j; rewrite !mxE. Qed.
Canonical Structure vec_mx_linear := LinearFun vec_mx_linear_proof.

Lemma mxvec_linear_proof : linear (@mxvec R m1 n1).
Proof. by move=> a A B; apply/rowP=> k; rewrite !(castmxE, mxE). Qed.
Canonical Structure mxvec_linear := LinearFun mxvec_linear_proof.

Lemma vec_mx_delta : forall i j,
  vec_mx (delta_mx 0 (mxvec_index i j)) = delta_mx i j :> 'M[R]_(m1, n1).
Proof.
move=> i j; apply/matrixP=> i' j'.
by rewrite !mxE /= [_ == _](inj_eq (@enum_rank_inj _)).
Qed.

Lemma mxvec_delta : forall i j,
  mxvec (delta_mx i j) = delta_mx 0 (mxvec_index i j) :> 'rV[R]_(m1 * n1).
Proof. by move=> i j; rewrite -vec_mx_delta vec_mxK. Qed.

End MoreLinear.

End Linear.

Notation "[ 'linear' 'of' f 'as' g ]" := (@clone_linear _ _ _ _ _ f g _ id _ id)
  (at level 0, format "[ 'linear'  'of'  f  'as'  g ]") : form_scope.

Notation "[ 'linear' 'of' f ]" := (@clone_linear _ _ _ _ _ f f _ id _ idfun)
  (at level 0, format "[ 'linear'  'of'  f ]") : form_scope.

Notation null_lin := (null_lin_head tt).
Notation add_lin := (add_lin_head tt).
Notation mulmxr := (mulmxr_head tt).
Implicit Arguments vec_mx_linear [R m1 n1].
Implicit Arguments mxvec_linear [R m1 n1].
Prenex Implicits vec_mx_linear mxvec_linear.

Section ComLinear.

Variables (R : comRingType) (m n p : nat).

Lemma scalemx_linear_proof : forall b : R, @linear _ m n m n (scalemx b).
Proof. by move=> b a u v; rewrite scalemx_addr !scalemxA mulrC. Qed.
Canonical Structure scalemx_linear b := LinearFun (scalemx_linear_proof b).

Lemma mulmx_linear_proof : forall A : 'M[R]_(m, n), @linear _ n p m p (mulmx A).
Proof. by move=> A a B C; rewrite mulmx_addr scalemxAr. Qed.
Canonical Structure mulmx_linear A := LinearFun (mulmx_linear_proof A).

End ComLinear.

(* Matrices of linear functions; in combination with mxvec/vec_mx this lets *)
(* us work with Hom-spaces.                                                 *)
Section LinMatrix.

Variable R : ringType.

Section RowLin.

Variables m n : nat.

Definition lin1_mx (f : 'rV[R]_m -> 'rV[R]_n) :=
  \matrix_(i, j) f (delta_mx 0 i) 0 j.

Variable f : linear_fun R 1 m 1 n.

Lemma mul_rV_lin1 : forall u, u *m lin1_mx f = f u.
Proof.
move=> u; rewrite {2}[u]matrix_sum_delta big_ord1 linear_sum; apply/rowP=> i.
by rewrite mxE summxE; apply: eq_bigr => j _; rewrite linearZ !mxE.
Qed.

End RowLin.

Variables m1 n1 m2 n2 : nat.

Definition lin_mx (f : 'M[R]_(m1, n1) -> 'M[R]_(m2, n2)) :=
  lin1_mx (mxvec \o f \o vec_mx).

Variable f : linear_fun R m1 n1 m2 n2.

Lemma mul_rV_lin : forall u, u *m lin_mx f = mxvec (f (vec_mx u)).
Proof. exact: mul_rV_lin1. Qed.

Lemma mul_vec_lin : forall A, mxvec A *m lin_mx f = mxvec (f A).
Proof. by move=> A; rewrite mul_rV_lin mxvecK. Qed.

Lemma mx_rV_lin : forall u, vec_mx (u *m lin_mx f) = f (vec_mx u).
Proof. by move=> A; rewrite mul_rV_lin mxvecK. Qed.

Lemma mx_vec_lin : forall A, vec_mx (mxvec A *m lin_mx f) = f A.
Proof. by move=> A; rewrite mul_rV_lin !mxvecK. Qed.

End LinMatrix.

(* Characterizing a scalar matrices, and the matrix subspaces that containing *)
(* nonscalar matrices.                                                        *)
Section ScalarMatrix.

Variables (F : fieldType) (n m : nat).

Definition is_scalar_mx (A : 'M[F]_n) := (mxvec A <= mxvec 1%:M)%MR.

Lemma is_scalar_mxP : forall A, reflect (exists a, A = a%:M) (is_scalar_mx A).
Proof.
move=> A; apply: (iffP (sub_rVP _ _)) => [[a] | [a ->]].
  by rewrite -linearZ scalemx1; move/(can_inj mxvecK); exists a.
by exists a; rewrite -linearZ scalemx1.
Qed.

Lemma scalar_mx_is_scalar : forall a, is_scalar_mx a%:M.
Proof. by move=> a; apply/is_scalar_mxP; exists a. Qed.

Lemma mx0_is_scalar : is_scalar_mx 0.
Proof. by rewrite /is_scalar_mx linear0 subset0mx. Qed.

Lemma has_non_scalar_mxP : forall E : 'M_(m, n * n), 
  reflect (exists2 A, mxvec A <= E & ~~ is_scalar_mx A)%MR
          ((mxvec 1%:M <= E)%MR < \rank E).
Proof.
move=> E; case: (eqVneq E 0) => [-> | nzE].
  rewrite mxrank0; right=> [[A]];  case/subsetmxP=> D; move/(canRL mxvecK)->.
  by rewrite !linear0 mx0_is_scalar.
case E_1: (_ <= E)%MR => /=; last first.
  rewrite lt0n mxrank_eq0 nzE; left.
  case/rowV0Pn: nzE => v svE nzv; exists (vec_mx v); first by rewrite vec_mxK.
  apply/is_scalar_mxP=> [[a]]; move/(canRL vec_mxK) => def_v; case/idP: E_1.
  rewrite def_v -scalemx1 linearZ eqmx_scale // in svE.
  by apply: contra nzv; rewrite def_v; move/eqP->; rewrite scalar_mx0 linear0.
have <-: (\rank (mxvec (1%:M : 'M[F]_n))).+1 = 2.
  apply/eqP; rewrite eqSS eqn_leq rank_leq_row lt0n mxrank_eq0.
  apply: contra nzE; move/eqP;  move/(congr1 (fun v => \rank (vec_mx v))).
  rewrite mxvecK mxrank1 linear0 mxrank0 => n0.
  by move: (E); rewrite n0 => E0; rewrite [E0]thinmx0.
rewrite ltn_neqAle andbC !mxrank_leqif_sup //=.
apply: (iffP idP) => [|[A sAE]]; last by apply: contra; exact: subsetmx_trans.
case/row_subPn=> i; rewrite -[row i E]vec_mxK; set A := vec_mx _ => nsA.
by exists A; rewrite // vec_mxK row_sub.
Qed.

End ScalarMatrix.

(* The centraliser of a (square n x n) matrix sub-algebra, represented as the *)
(* row space of an n^2 x n^2 matrix; this is commonly denoted Hom_A(V).       *)
Section CentMx.

Variables (F : fieldType) (n m : nat) (E : 'M[F]_(m, n * n)).

Definition cent_mx_fun (B : 'M[F]_n) :=
  E *m lin_mx (add_lin (mulmxr B) (-%R \o mulmx B)).

Lemma cent_mx_linear_proof : linear cent_mx_fun.
Proof.
move=> a A B; apply/row_matrixP=> i; rewrite linearP row_mul mul_rV_lin.
rewrite /= {-3}[row]lock row_mul mul_rV_lin -lock row_mul mul_rV_lin -linearP.
by rewrite -(linearP [linear of add_lin (mulmx _) (-%R \o mulmxr _)]).
Qed.
Canonical Structure cent_mx_linear := LinearFun cent_mx_linear_proof.

Definition cent_mx := kermx (lin_mx cent_mx_fun).

Lemma subset_cent_rowP : forall B,
  reflect (forall i (A := vec_mx (row i E)), A *m B = B *m A)
          (mxvec B <= cent_mx)%MR.
Proof.
move=> B; apply: (iffP (subsetmx_kerP _ _)); rewrite mul_vec_lin => cBE.
  move/(canRL mxvecK): cBE => cBE i A /=; move/(congr1 (row i)): cBE.
  rewrite row_mul mul_rV_lin -/A; move/(canRL mxvecK).
  by move/(canRL (subrK _)); rewrite !linear0 add0r.
apply: (canLR vec_mxK); apply/row_matrixP=> i.
by rewrite row_mul mul_rV_lin /= cBE subrr !linear0.
Qed.

Lemma subset_cent_mxP : forall B,
  reflect (forall A, mxvec A <= E -> A *m B = B *m A)%MR
          (mxvec B <= cent_mx)%MR.
Proof.
move=> B; apply: (iffP (subset_cent_rowP B)) => cEB => [A sAE | i A].
  rewrite -[A]mxvecK -(mulmxKpV sAE); move: (mxvec A *m _) => u.
  rewrite !mulmx_sum_row !linear_sum mulmx_suml; apply: eq_bigr => i _ /=.
  by rewrite !linearZ -scalemxAl /= cEB.
by rewrite cEB // vec_mxK row_sub.
Qed.

Lemma scalar_mx_cent : forall a, (mxvec a%:M <= cent_mx)%MR.
Proof. by move=> a; apply/subset_cent_mxP=> A _; exact: scalar_mxC. Qed.

End CentMx.

(* Row vector <-> bounded degree polynomial bijection *)
Section RowPoly.

Variables (R : ringType) (d : nat).
Implicit Types u v : 'rV[R]_d.
Implicit Types p q : {poly R}.

Definition rVpoly v := \poly_(k < d) (if insub k is Some i then v 0 i else 0).
Definition poly_rV p := \row_(i < d) p`_i.

Lemma coef_rVpoly : forall v k,
  (rVpoly v)`_k = if insub k is Some i then v 0 i else 0.
Proof.
by move=> v k; rewrite coef_poly; case: insubP => [i ->|]; rewrite ?if_same.
Qed.

Lemma coef_rVpoly_ord : forall v (i : 'I_d), (rVpoly v)`_i = v 0 i.
Proof. by move=> v i; rewrite coef_rVpoly valK. Qed.

Lemma rVpolyK : cancel rVpoly poly_rV.
Proof. by move=> u; apply/rowP=> i; rewrite mxE coef_rVpoly_ord. Qed.

Lemma poly_rV_K : forall p, size p <= d -> rVpoly (poly_rV p) = p.
Proof.
move=> p le_p_d; apply/polyP=> k; rewrite coef_rVpoly.
case: insubP => [i _ <- | ]; first by rewrite mxE.
by rewrite -ltnNge => le_d_l; rewrite nth_default ?(leq_trans le_p_d).
Qed.

Lemma poly_rV_0 : poly_rV 0 = 0.
Proof. by apply/rowP=> i; rewrite !mxE coef0. Qed.

Lemma poly_rV_N : {morph poly_rV : p / - p}.
Proof. by move=> p; apply/rowP=> i; rewrite !mxE coef_opp. Qed.

Lemma poly_rV_D : {morph poly_rV : p q / p + q}.
Proof. by move=> p q; apply/rowP=> i; rewrite !mxE coef_add. Qed.

Lemma rVpoly0 : rVpoly 0 = 0.
Proof.
by apply/polyP=> k; rewrite coef_rVpoly coef0; case: insubP => *; rewrite ?mxE.
Qed.

Lemma rVpolyN : {morph rVpoly : u / - u}.
Proof.
move=> u; apply/polyP=> k; rewrite coef_opp !coef_rVpoly.
by case: insubP => [i _ _ | _]; rewrite ?mxE ?oppr0.
Qed.

Lemma rVpolyD : {morph rVpoly : u v / u + v}.
Proof.
move=> u v; apply/polyP=> k; rewrite coef_add !coef_rVpoly.
by case: insubP => [i _ _ | _]; rewrite ?mxE ?addr0.
Qed.

End RowPoly.

Implicit Arguments poly_rV [R d].
Prenex Implicits rVpoly poly_rV.

(* The minimal polynomial of a matrix, and some of its properties.           *)
(* We assume non-trivial matrices here.                                      *)
Section MinPoly.

Variables (F : fieldType) (n' : nat).
Local Notation n := n'.+1.
Variable A : 'M[F]_n.
Implicit Types p q : {poly F}.

Definition horner_mx := horner_morph scalar_mx A.

Let zRM := @scalar_mxRM F n'.
Let mx_pRM := map_polyRM zRM.

Lemma horner_mxRM : GRing.morphism horner_mx.
Proof. apply: horner_morphRM => // a; exact: scalar_mx_comm. Qed.
Hint Resolve horner_mxRM.

Lemma horner_mx_C : forall a, horner_mx a%:P = a%:M.
Proof. exact: horner_morphC. Qed.

Lemma horner_mx_X : horner_mx 'X = A. Proof. exact: horner_morphX. Qed.

Lemma horner_mx_Xn : forall k, horner_mx 'X^k = A ^+ k.
Proof. by move=> k; rewrite ringM_exp ?horner_mx_X. Qed.

Lemma horner_mx_CXn : forall a k, horner_mx (a%:P * 'X^k) = a *m: A ^+ k.
Proof.
move=> a k; rewrite ringM_mul //.
by rewrite horner_mx_C horner_mx_Xn [_ * _]mul_scalar_mx.
Qed.

Definition minpoly_mx d := \matrix_(i < d) mxvec (A ^+ i).

Lemma horner_rVpoly : forall m (u : 'rV_m),
  horner_mx (rVpoly u) = vec_mx (u *m minpoly_mx m).
Proof.
move=> m u; rewrite mulmx_sum_row linear_sum [rVpoly u]poly_def ringM_sum //.
by apply: eq_bigr => i _; rewrite valK horner_mx_CXn linearZ rowK /= mxvecK.
Qed.

Lemma degree_mxminpoly_proof : exists d, \rank (minpoly_mx d.+1) <= d.
Proof. by exists (n ^ 2)%N; rewrite rank_leq_col. Qed.
Definition degree_mxminpoly := ex_minn degree_mxminpoly_proof.
Local Notation d := degree_mxminpoly.
Local Notation Ad := (minpoly_mx d).

Lemma mxminpoly_nonconstant : d > 0.
Proof.
rewrite /d; case: ex_minnP; case=> //; rewrite leqn0 mxrank_eq0; move/eqP.
move/row_matrixP; move/(_ 0); rewrite rowK row0; move/(canRL mxvecK); move/eqP.
by rewrite linear0 -mxrank_eq0 mxrank1.
Qed.

Lemma minpoly_mx_free : row_free Ad.
Proof.
have:= mxminpoly_nonconstant; rewrite /d; case: ex_minnP; case=> // d' _.
move/(_ d'); move/implyP; rewrite ltnn implybF -ltnS ltn_neqAle.
by rewrite rank_leq_row andbT negbK.
Qed.

Lemma horner_mx_sub : forall p, (mxvec (horner_mx p) <= Ad)%MR.
Proof.
elim/poly_ind=> [|p a IHp]; first by rewrite ringM_0 // linear0 subset0mx.
rewrite ringM_add // ringM_mul // horner_mx_C horner_mx_X.
rewrite addrC -scalemx1 linearP /= -(mul_vec_lin (mulmxr_linear _ A)).
case/subsetmxP: IHp => u ->{i}.
have: (minpoly_mx (1 + d) <= Ad)%MR.
  rewrite -(geq_leqif (mxrank_leqif_sup _)).
    by rewrite (eqnP minpoly_mx_free) /d; case: ex_minnP.
  rewrite addnC; apply/row_subP=> {i}i.
  by apply: eq_row_sub (lshift 1 i) _; rewrite !rowK.
apply: subsetmx_trans; rewrite subsetmx_add ?subsetmx_scale //.
  by apply: (eq_row_sub 0); rewrite rowK.
rewrite -mulmxA subsetmxMtrans {u}//; apply/row_subP=> i.
rewrite row_mul rowK mul_vec_lin /= mulmxE -exprSr.
by apply: (eq_row_sub (rshift 1 i)); rewrite rowK.
Qed.

Definition mx_inv_horner B := rVpoly (mxvec B *m pinvmx Ad).

Lemma mx_inv_horner0 :  mx_inv_horner 0 = 0.
Proof. by rewrite /mx_inv_horner linear0 mul0mx rVpoly0. Qed.

Lemma mx_inv_hornerK : forall B,
  (mxvec B <= Ad)%MR -> horner_mx (mx_inv_horner B) = B.
Proof. by move=> B sBAd; rewrite horner_rVpoly mulmxKpV ?mxvecK. Qed.

Definition mxminpoly := 'X^d - mx_inv_horner (A ^+ d).
Local Notation p_A := mxminpoly.

Lemma size_mxminpoly : size p_A = d.+1.
Proof. by rewrite size_addl ?size_polyXn // size_opp ltnS size_poly. Qed.

Lemma mxminpoly_monic : monic p_A.
Proof.
rewrite /monic /lead_coef size_mxminpoly coef_sub coef_Xn eqxx /=.
by rewrite nth_default ?size_poly // subr0.
Qed.

Lemma size_mod_mxminpoly : forall p, size (p %% p_A) <= d.
Proof.
move=> p; rewrite -ltnS -size_mxminpoly modp_spec //.
by rewrite -size_poly_eq0 size_mxminpoly.
Qed.

Lemma mx_root_minpoly : horner_mx p_A = 0.
Proof.
by rewrite ringM_sub // -horner_mx_Xn mx_inv_hornerK ?subrr ?horner_mx_sub.
Qed.

Lemma horner_rVpolyK : forall u : 'rV_d,
  mx_inv_horner (horner_mx (rVpoly u)) = rVpoly u.
Proof.
case/row_freeP: minpoly_mx_free => Ad' AdK u; congr rVpoly.
rewrite horner_rVpoly vec_mxK -[_ *m _]mulmx1 -AdK mulmxA.
by rewrite mulmxKpV ?subsetmxMl // -mulmxA AdK mulmx1.
Qed.

Lemma horner_mxK : forall p, mx_inv_horner (horner_mx p) = p %% p_A.
Proof.
move=> p; rewrite {1}(divp_mon_spec p mxminpoly_monic) ringM_add ?ringM_mul //.
rewrite mx_root_minpoly mulr0 add0r.
by rewrite -(poly_rV_K (size_mod_mxminpoly _)) horner_rVpolyK.
Qed.

Lemma mxminpoly_min : forall p, horner_mx p = 0 -> p_A %| p.
Proof. by move=> p pA0; rewrite /dvdp -horner_mxK pA0 mx_inv_horner0. Qed.

Lemma horner_rVpoly_inj : @injective 'M_n 'rV_d (horner_mx \o rVpoly).
Proof.
apply: can_inj (poly_rV \o mx_inv_horner) _ => u.
by rewrite /= horner_rVpolyK rVpolyK.
Qed.

Lemma mxminpoly_linear_is_scalar : (d <= 1) = is_scalar_mx A.
Proof.
have:= has_non_scalar_mxP Ad; rewrite -horner_mx_C horner_mx_sub => scalP.
rewrite leqNgt -(eqnP minpoly_mx_free); apply/scalP/idP=> [|[[B]]].
  case scalA: (is_scalar_mx A); [by right | left].
  by exists A; rewrite ?scalA // -horner_mx_X horner_mx_sub.
move/mx_inv_hornerK=> <- nsB; case/is_scalar_mxP=> a defA; case/negP: nsB.
elim/poly_ind: {B}(_ B) => [|p c]; first by rewrite ringM_0 ?mx0_is_scalar.
rewrite ringM_add ?ringM_mul // horner_mx_X defA; case/is_scalar_mxP=> b ->.
by rewrite -(ringM_mul zRM) horner_mx_C -scalar_mx_add scalar_mx_is_scalar.
Qed.

End MinPoly.

Section GenRepr.

Variable F : fieldType.

Section Representation.

Variable gT : finGroupType.

Definition mx_repr (G : {set gT}) n (r : gT -> 'M[F]_n) :=
  r 1%g = 1%:M /\ {in G &, {morph r : x y / (x * y)%g >-> x *m y}}.

Structure mx_representation G n :=
  MxRepresentation { repr_mx :> gT -> 'M_n; _ : mx_repr G repr_mx }.

Variables (G : {group gT}) (n : nat) (rG : mx_representation G n).
Arguments Scope rG [group_scope].

Lemma repr_mx1 : rG 1 = 1%:M. Proof. by case: rG => r []. Qed.
Lemma repr_mxM : {in G &, {morph rG : x y / (x * y)%g >-> x *m y}}.
Proof. by case: rG => r []. Qed.

Lemma repr_mxK : forall m x,
  x \in G -> cancel ((@mulmx _ m n n)^~ (rG x)) (mulmx^~ (rG x^-1)).
Proof.
by move=> m x Gx U; rewrite -mulmxA -repr_mxM ?groupV // mulgV repr_mx1 mulmx1.
Qed.

Lemma repr_mxKV : forall m x,
  x \in G -> cancel ((@mulmx _ m n n)^~ (rG x^-1)) (mulmx^~ (rG x)).
Proof. move=> m x; rewrite -groupV -{3}[x]invgK; exact: repr_mxK. Qed.

Lemma repr_mx_unit : forall x, x \in G -> rG x \in unitmx.
Proof. by move=> x Gx; case/mulmx1_unit: (repr_mxKV Gx 1%:M). Qed.

Lemma repr_mxV : {in G, {morph rG : x / (x^-1)%g >-> invmx x}}.
Proof.
by move=> x Gx /=; rewrite -[rG x^-1](mulKmx (repr_mx_unit Gx)) mulmxA repr_mxK.
Qed.

Definition enveloping_algebra_mx :=
   \matrix_(i, j) mxvec (rG (@sgval _ G (enum_val i))) 0 j.
Local Notation E_G := enveloping_algebra_mx.

Lemma row_envelopI : forall x, x \in G -> {i | rG x = vec_mx (row i E_G)}.
Proof.
move=> x Gx; exists (enum_rank (subg G x)).
by rewrite rowK enum_rankK mxvecK subgK.
Qed.

Lemma row_envelopE : forall i, {x | x \in G & row i E_G = mxvec (rG x)}.
Proof. by move=> i; exists (val (enum_val i)); rewrite ?subgP // rowK. Qed.

Definition rfix_mx_fun (u : 'rV_n) := E_G *m lin1_mx (mulmx u \o vec_mx).
Lemma rfix_mx_fun_linear_proof : linear rfix_mx_fun.
Proof.
move=> a u v; apply/row_matrixP=> i; rewrite linearP /=.
by rewrite !row_mul !mul_rV_lin1 /= -(linearP (mulmxr_linear _ _)).
Qed.
Canonical Structure rfix_mx_fun_linear := LinearFun rfix_mx_fun_linear_proof.

Definition rfix_mx :=
  kermx (lin1_mx (mxvec \o (add_lin rfix_mx_fun (-%R \o mulmx (const_mx 1))))).

Lemma subsetmx_rfixP : forall m (W : 'M_(m, n)),
  reflect (forall x, x \in G -> W *m rG x = W) (W <= rfix_mx)%MR.
Proof.
move=> m W; apply: (iffP (subsetmx_kerP _ _)) => [cWG x Gx | cWG].
  apply/row_matrixP=> i; move/row_matrixP: cWG; move/(_ i).
  rewrite !row_mul mul_rV_lin1 /=; move/(canRL mxvecK); rewrite !linear0.
  case/row_envelopI: Gx => j ->{x}; move/row_matrixP; move/(_ j).
  rewrite row0 linear_sub /= !row_mul mul_rV_lin1 /=; move/(canRL (subrK _))->.
  by rewrite add0r /= [row j _]mx11_scalar !mxE mul1mx.
apply/row_matrixP=> i; rewrite row_mul mul_rV_lin1 /=; apply: (canLR vec_mxK).
apply/row_matrixP=> j; rewrite linear_sub !linear0 /= !row_mul mul_rV_lin1 /=.
rewrite [row j (_ 1)]mx11_scalar !mxE mul1mx -row_mul.
by have [x Gx ->]:= row_envelopE j; rewrite mxvecK cWG ?subrr.
Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Definition rstab := [set x \in G | U *m rG x == U].
Definition rstabs := [set x \in G | U *m rG x <= U]%MR.

Lemma rstab_sub : rstab \subset G.
Proof. by apply/subsetP=> x; case/setIdP. Qed.

Lemma rstabs_sub : rstabs \subset G.
Proof. by apply/subsetP=> x; case/setIdP. Qed.

Lemma rstabs_group_set : group_set rstabs.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1; split=> //= x y.
case/setIdP=> Gx nUx; case/setIdP=> Gy; rewrite inE repr_mxM ?groupM //.
by apply: subsetmx_trans; rewrite mulmxA subsetmxMr.
Qed.
Canonical Structure rstabs_group := Group rstabs_group_set.

Lemma rstab_group_set : group_set rstab.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1; split=> //= x y.
case/setIdP=> Gx cUx; case/setIdP=> Gy cUy; rewrite inE repr_mxM ?groupM //.
by rewrite mulmxA (eqP cUx).
Qed.
Canonical Structure rstab_group := Group rstab_group_set.

Lemma rstab_act : forall x m1 (W : 'M_(m1, n)),
  x \in rstab -> (W <= U)%MR -> W *m rG x = W.
Proof.
move=> x m1 W; case/setIdP=> _; move/eqP=> cUx.
by case/subsetmxP=> w ->; rewrite -mulmxA cUx.
Qed.

Lemma rstabs_act : forall x m1 (W : 'M_(m1, n)),
  x \in rstabs -> (W <= U)%MR -> (W *m rG x <= U)%MR.
Proof.
move=> x m1 W; case/setIdP=> _ nUx sWU; apply: subsetmx_trans nUx.
exact: subsetmxMr.
Qed.

End Stabilisers.

Lemma rstabS : forall m1 m2 U V, (U <= V)%MR -> @rstab m2 V \subset @rstab m1 U.
Proof.
move=> m1 m2 U V; case/subsetmxP=> u ->; apply/subsetP=> x; rewrite !inE.
by case/andP=> -> /= cVx; rewrite -mulmxA (eqP cVx).
Qed.

Lemma eqmx_rstab : forall m1 m2 U V, (U :=: V)%MR -> @rstab m1 U = @rstab m2 V.
Proof.
by move=> m1 m2 U V eqUV; apply/eqP; rewrite eqEsubset !rstabS ?eqUV.
Qed.

Lemma eqmx_rstabs : forall m1 m2 U V,
  (U :=: V)%MR -> @rstabs m1 U = @rstabs m2 V.
Proof.
by move=> m1 m2 U V eqUV; apply/setP=> x; rewrite !inE eqUV (eqmxMr _ eqUV).
Qed.

Section SubModule.


Variable U : 'M[F]_n.

Definition rcent := [set x \in G | U *m rG x == rG x *m U].

Lemma rcent_sub : rcent \subset G.
Proof. by apply/subsetP=> x; case/setIdP. Qed.

Lemma rcent_group_set : group_set rcent.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1 mul1mx; split=> //= x y.
case/setIdP=> Gx; move/eqP=> cUx; case/setIdP=> Gy; move/eqP=> cUy.
by rewrite inE repr_mxM ?groupM //= -mulmxA -cUy !mulmxA cUx.
Qed.
Canonical Structure rcent_group := Group rcent_group_set.

Definition centgmx := G \subset rcent.

Lemma centgmxP : reflect (forall x, x \in G -> U *m rG x = rG x *m U) centgmx.
Proof.
apply: (iffP subsetP) => cGU x Gx;
  by have:= cGU x Gx; rewrite !inE Gx /=; move/eqP.
Qed.

Lemma subsetmx_cent_envelop : (mxvec U <= cent_mx E_G)%MR = centgmx.
Proof.
apply/subset_cent_rowP/centgmxP=> [cUG x Gx | cUG i].
  by have [i ->] := row_envelopI Gx; rewrite cUG.
by rewrite rowK mxvecK /= cUG ?subgP.
Qed.

Definition submodmx := G \subset rstabs U.

Lemma submodmxP : reflect (forall x, x \in G -> U *m rG x <= U)%MR submodmx.
Proof.
by apply: (iffP subsetP) => modU x Gx; have:= modU x Gx; rewrite !inE ?Gx.
Qed.

Definition val_submod m : 'M_(m, \rank U) -> 'M_(m, n) := mulmxr (row_base U).
Definition in_submod m : 'M_(m, n) -> 'M_(m, \rank U) :=
   mulmxr (invmx (row_ebase U) *m pid_mx (\rank U)).
Canonical Structure val_submod_linear m := [linear of @val_submod m].
Canonical Structure in_submod_linear m := [linear of @in_submod m].

Lemma val_submodP : forall m W, (@val_submod m W <= U)%MR.
Proof. by move=> m W; rewrite subsetmxMtrans ?eq_row_base. Qed.

Lemma val_submodK : forall m, cancel (@val_submod m) (@in_submod m).
Proof.
move=> w W; rewrite /in_submod /= -!mulmxA mulKVmx ?row_ebase_unit //.
by rewrite pid_mx_id ?rank_leq_row // pid_mx_1 mulmx1.
Qed.

Lemma val_submod_inj : forall m, injective (@val_submod m).
Proof. move=> m; exact: can_inj (@val_submodK m). Qed.

Lemma val_submodS : forall m1 m2 (V : 'M_(m1, \rank U)) (W : 'M_(m2, \rank U)),
  (val_submod V <= val_submod W)%MR = (V <= W)%MR.
Proof.
move=> m1 m2 V W; apply/idP/idP=> sVW; last exact: subsetmxMr.
by rewrite -[V]val_submodK -[W]val_submodK subsetmxMr.
Qed.

Lemma in_submodK : forall m W, (W <= U)%MR -> val_submod (@in_submod m W) = W.
Proof.
move=> m W; case/subsetmxP=> w ->; rewrite /val_submod /= -!mulmxA.
congr (_ *m _); rewrite -{1}[U]mulmx_ebase !mulmxA mulmxK ?row_ebase_unit //.
by rewrite -2!(mulmxA (col_ebase U)) !pid_mx_id ?rank_leq_row // mulmx_ebase.
Qed.

Lemma in_submod_eq0 : forall m W, (@in_submod m W == 0) = (W <= U^C)%MR.
Proof.
move=> m W; apply/eqP/subsetmxP=> [W_U0 | [w ->{W}]].
  exists (W *m invmx (row_ebase U)).
  rewrite mulmxA mulmx_subr mulmx1 -(pid_mx_id _ _ _ (leqnn _)).
  rewrite mulmxA -(mulmxA W) [W *m (_ *m _)]W_U0 mul0mx subr0.
  by rewrite mulmxKV ?row_ebase_unit.
rewrite /in_submod /= -!mulmxA mulKVmx ?row_ebase_unit //.
by rewrite mul_copid_mx_pid ?rank_leq_row ?mulmx0.
Qed.
  
Definition val_factmod m : _ -> 'M_(m, n) :=
  mulmxr (row_base (cokermx U) *m row_ebase U).
Definition in_factmod m : 'M_(m, n) -> _ := mulmxr (col_base (cokermx U)).
Canonical Structure val_factmod_linear m := [linear of @val_factmod m].
Canonical Structure in_factmod_linear m := [linear of @in_factmod m].

Lemma val_factmodP : forall m W, (@val_factmod m W <= U^C)%MR.
Proof.
move=> m W; rewrite subsetmxMtrans {m W}// -[_ *m _]mul1mx.
case/row_fullP: (col_base_full (cokermx U)) => Uc' <-.
by rewrite -mulmxA subsetmxMtrans {Uc'}// mulmxA mulmx_base -mulmxA subsetmxMl.
Qed.

Lemma val_factmodK : forall m, cancel (@val_factmod m) (@in_factmod m).
Proof.
move=> m W /=; rewrite /in_factmod /=; set Uc := cokermx U. 
case/row_freeP: (row_base_free Uc) => Uc' UcK; rewrite -{1}[_ *m _]mulmx1 -UcK.
rewrite -mulmxA (mulmxA _ _ Uc') mulmx_base -2!mulmxA.
rewrite -(mulmxA _ _ Uc') mulKVmx ?row_ebase_unit //.
have: (row_base Uc <= Uc)%MR by rewrite eq_row_base.
case/subsetmxP=> u defUcr; rewrite defUcr -mulmxA (mulmxA Uc) -[Uc *m _]mulmxA.
by rewrite copid_mx_id ?rank_leq_row // (mulmxA u) -defUcr UcK mulmx1.
Qed.

Lemma val_factmod_inj : forall m, injective (@val_factmod m).
Proof. move=> m; exact: can_inj (@val_factmodK m). Qed.

Lemma val_factmodS : forall m1 m2 (V : 'M_(m1, _)) (W : 'M_(m2, _)),
  (val_factmod V <= val_factmod W)%MR = (V <= W)%MR.
Proof.
move=> m1 m2 V W; apply/idP/idP=> sVW; last exact: subsetmxMr.
by rewrite -[V]val_factmodK -[W]val_factmodK subsetmxMr.
Qed.

Lemma in_factmod_eq0 : forall m (W : 'M_(m, n)),
  (in_factmod W == 0) = (W <= U)%MR.
Proof.
move=> m W; unlock subsetmx; rewrite -!mxrank_eq0 -{2}[_ U]mulmx_base mulmxA.
by rewrite (mxrankMfree _ (row_base_free _)).
Qed.

Lemma in_factmodK : forall m (W : 'M_(m, n)),
  (W <= U^C)%MR -> val_factmod (in_factmod W) = W.
Proof.
move=> m W; case/subsetmxP=> w ->{W}; rewrite /val_factmod /= -2!mulmxA.
congr (_ *m _); rewrite (mulmxA (col_base _)) mulmx_base -2!mulmxA.
by rewrite mulKVmx ?row_ebase_unit // mulmxA copid_mx_id ?rank_leq_row.
Qed.

Lemma sum_sub_fact_mod : forall m (W : 'M_(m, n)),
   val_submod (in_submod W) + val_factmod (in_factmod W) = W.
Proof.
move=> m W; rewrite /val_submod /val_factmod /= -!mulmxA -mulmx_addr.
rewrite addrC (mulmxA (pid_mx _)) pid_mx_id // (mulmxA (col_ebase _)).
rewrite (mulmxA _ _ (row_ebase _)) mulmx_ebase.
rewrite (mulmxA (pid_mx _)) pid_mx_id // mulmxA -mulmx_addl -mulmx_addr.
by rewrite subrK mulmx1 mulmxA mulmxKV ?row_ebase_unit.
Qed.

Definition submod_mx of submodmx :=
  fun x => in_submod (row_base U *m rG x).

Definition factmod_mx of submodmx :=
  fun x => in_factmod ((val_factmod 1%:M) *m rG x).

Hypothesis Umod : submodmx.

Lemma in_submodJ : forall m (W : 'M_(m, n)) x,
  (W <= U)%MR -> in_submod (W *m rG x) = in_submod W *m submod_mx Umod x.
Proof.
by move=> m W x sWU; rewrite mulmxA (mulmxA _ _ (rG x)) -{1}(in_submodK sWU).
Qed.

Lemma val_submodJ : forall m (W : 'M_(m, \rank U)) x,
  x \in G -> val_submod (W *m submod_mx Umod x) = val_submod W *m rG x.
Proof.
move=> m W x Gx; rewrite -{1}[W]val_submodK -in_submodJ ?val_submodP //.
rewrite in_submodK // -mulmxA subsetmxMtrans //.
by rewrite (eqmxMr _ (eq_row_base U)) (submodmxP Umod).
Qed.

Lemma submod_mx_repr : mx_repr G (submod_mx Umod).
Proof.
rewrite /submod_mx; split=> [|x y Gx Gy /=].
  by rewrite repr_mx1 scalar_mxC val_submodK.
rewrite -in_submodJ; first by rewrite repr_mxM ?mulmxA.
by rewrite (eqmxMr _ (eq_row_base U)) (submodmxP Umod).
Qed.
Canonical Structure submod_repr := MxRepresentation submod_mx_repr.

Lemma in_factmodJ : forall m (W : 'M_(m, n)) x,
  x \in G -> in_factmod (W *m rG x) = in_factmod W *m factmod_mx Umod x.
Proof.
move=> m W x Gx; rewrite -{1}[W]sum_sub_fact_mod mulmx_addl linearD /=.
apply: (canLR (subrK _)); apply: etrans (_ : 0 = _).
  apply/eqP; rewrite in_factmod_eq0 (subsetmx_trans _ (submodmxP Umod x Gx)) //.
  by rewrite subsetmxMr ?val_submodP.
by rewrite /in_factmod /val_factmod /= !mulmxA mulmx1 ?subrr.
Qed.

Lemma val_factmodJ : forall m (W : 'M_(m, \rank (cokermx U))) x,
  x \in G ->
  val_factmod (W *m factmod_mx Umod x) =
     val_factmod (in_factmod (val_factmod W *m rG x)).
Proof. by move=> m W x Gx; rewrite -{1}[W]val_factmodK -in_factmodJ. Qed.

Lemma factmod_mx_repr : mx_repr G (factmod_mx Umod).
Proof.
split=> [|x y Gx Gy /=].
  by rewrite /factmod_mx repr_mx1 mulmx1 val_factmodK.
by rewrite -in_factmodJ // -mulmxA -repr_mxM.
Qed.
Canonical Structure factmod_repr := MxRepresentation factmod_mx_repr.

End SubModule.

Lemma rfix_submodmx : submodmx rfix_mx.
Proof.
apply/submodmxP=> x Gx; apply/row_subP=> i.
by rewrite row_mul (subsetmx_rfixP _ _) ?row_sub.
Qed.

Lemma mx_Maeshke : forall U,
    [char F]^'.-group G -> submodmx U ->
  {W : 'M_n | [/\ submodmx W, row_full (U :+: W) & U :&: W = 0]}%MR.
Proof.
rewrite /pgroup charf'_nat; set nG := _%:R => U nzG; move/submodmxP=> Umod.
pose phi := nG^-1 *m: (\sum_(x \in G) rG x^-1 *m pinvmx U *m U *m rG x).
have phiG: forall x, x \in G -> phi *m rG x = rG x *m phi.
  move=> x Gx; rewrite -scalemxAl -scalemxAr; congr (_ *m: _).
  rewrite {2}(reindex_acts 'R _ Gx) ?astabsR //= mulmx_suml mulmx_sumr.
  apply: eq_bigr => y Gy; rewrite !mulmxA -repr_mxM ?groupV ?groupM //.
  by rewrite invMg mulKVg repr_mxM ?mulmxA.
have Uphi: U *m phi = U.
  rewrite -scalemxAr mulmx_sumr (eq_bigr (fun _ => U)) => [|x Gx].
    by rewrite sumr_const -scalemx_nat scalemxA mulVf ?scale1mx.
  by rewrite 3!mulmxA mulmxKpV ?repr_mxKV ?Umod ?groupV.
have tiUker: (U :&: kermx phi = 0)%MR.
  apply/eqP; apply/rowV0P=> v; rewrite sub_capmx; case/andP.
  by case/subsetmxP=> u ->; move/subsetmx_kerP; rewrite -mulmxA Uphi.
exists (kermx phi); split=> //.
  apply/submodmxP=> x Gx; apply/subsetmx_kerP.
  by rewrite -mulmxA -phiG // mulmxA mulmx_ker mul0mx.
rewrite /row_full mxrank_direct_sum // mxrank_ker.
suffices ->: (U :=: phi)%MR by rewrite subnKC ?rank_leq_row.
apply/eqmxP; rewrite -{1}Uphi subsetmxMl subsetmx_scale //.
by rewrite subsetmx_sum // => x Gx; rewrite -mulmxA subsetmxMtrans ?Umod.
Qed.

Definition mx_reducible := n > 0 -> exists U, submodmx U && (0 < \rank U < n).

Definition mx_irreducible := ~ mx_reducible.

Lemma mx_irrP :
   mx_irreducible <-> n > 0 /\ (forall U, submodmx U -> U != 0 -> row_full U).
Proof.
split=> [irrG | [_ irrG] [// | U]].
  split=> [|U Umod Unz]; apply/negP=> redG; case: irrG => _ //.
  exists U; rewrite Umod lt0n mxrank_eq0 Unz ltnNge col_leq_rank; exact/negP.
by rewrite lt0n mxrank_eq0 ltnNge col_leq_rank; case/and3P=> Umod; move/irrG->.
Qed.

Lemma centgmx_ker_submod : forall A, centgmx A -> submodmx (kermx A).
Proof.
move=> A; move/centgmxP=> cAG; apply/submodmxP=> x Gx; apply/subsetmx_kerP.
by rewrite -mulmxA -cAG // mulmxA mulmx_ker mul0mx.
Qed.

(* We only have the endomorphism part of Schur's lemma since we only defined *)
(* commutation for matrices, which implicitly represent endomorphisms.       *)
Lemma mx_Schur : mx_irreducible -> forall A, centgmx A -> A = 0 \/ A \in unitmx.
Proof.
move=> irrG A cAG; case: (eqVneq A 0) => [| nzA]; [by left | right].
apply/idPn; rewrite -row_full_unit -col_leq_rank -subn_eq0 => ntK.
case: irrG => n_gt0; exists (kermx A); rewrite centgmx_ker_submod //=.
by rewrite mxrank_ker lt0n ntK -subn_gt0 lt0n subKn ?rank_leq_row ?mxrank_eq0.
Qed.

Definition rker := rstab 1%:M.
Canonical Structure rker_group := Eval hnf in [group of rker].

Lemma rkerP : forall x, reflect (x \in G /\ rG x = 1%:M) (x \in rker).
Proof.
by move=> x; apply: (iffP setIdP) => [] [->]; move/eqP; rewrite mul1mx.
Qed.

Lemma rker_norm : G \subset 'N(rker).
Proof.
apply/subsetP=> x Gx; rewrite inE sub_conjg; apply/subsetP=> y.
case/rkerP=> Gy ry1; rewrite mem_conjgV !inE groupJ //=.
by rewrite !repr_mxM ?groupM ?groupV // ry1 !mulmxA mulmx1 repr_mxKV.
Qed.

Lemma rker_normal : rker <| G.
Proof. by rewrite /normal rstab_sub rker_norm. Qed.

Definition mx_repr_faithful := rker \subset [1].

Definition mx_absolutely_irreducible := (n > 0) && row_full E_G.

Lemma mx_abs_irrP :
  reflect (n > 0 /\ exists a_, forall A, A = \sum_(x \in G) a_ x A *m: rG x)
          mx_absolutely_irreducible.
Proof.
pose toI x := enum_rank (subg G x); pose ofI i := @sgval _ G (enum_val i).
have ofIK: cancel ofI toI by move=> i; rewrite /toI sgvalK enum_valK.
have ofIbij: {on (mem G), bijective ofI}.
  by exists toI => [i _ // | x Gx]; rewrite /ofI enum_rankK subgK.
rewrite /mx_absolutely_irreducible; case: (n > 0); last by right; case.
apply: (iffP (row_fullP _)) => [[E' E'G] | [_ [a_ a_G]]].
  split=> //; exists (fun x B => (mxvec B *m E') 0 (toI x)) => B.
  apply: (can_inj mxvecK); rewrite -{1}[mxvec B]mulmx1 -{}E'G mulmxA.
  move: {B E'}(_ *m E') => u; apply/rowP=> j.
  rewrite linear_sum (reindex ofI) //= mxE summxE.
  by apply: eq_big => [k| k _]; [rewrite subgP | rewrite ofIK mxE linearZ !mxE].
exists (\matrix_(j, i) a_ (ofI i) (vec_mx (row j 1%:M))).
apply/row_matrixP=> i; rewrite -[row i 1%:M]vec_mxK {}[vec_mx _]a_G.
apply/rowP=> j; rewrite linear_sum (reindex ofI) //= 2!mxE summxE.
by apply: eq_big => [k| k _]; [rewrite subgP | rewrite linearZ !mxE].
Qed.

Lemma mx_abs_irr_cent_scalar :
  mx_absolutely_irreducible -> forall A, centgmx A -> is_scalar_mx A.
Proof.
case/mx_abs_irrP=> n_gt0 [a_ a_G] A; move/centgmxP=> cGA.
have{cGA a_G} cMA: forall B : 'M_n, A *m B = B *m A.
  move=> B; rewrite {}[B]a_G mulmx_suml mulmx_sumr.
  by apply: eq_bigr => x Gx; rewrite -scalemxAl -scalemxAr cGA.
pose i0 := Ordinal n_gt0; apply/is_scalar_mxP; exists (A i0 i0).
apply/matrixP=> i j; move/matrixP: (esym (cMA (delta_mx i0 i))); move/(_ i0 j).
rewrite -[A *m _]trmxK trmx_mul trmx_delta -!(@mul_delta_mx _ n 1 n 0) -!mulmxA.
by rewrite -!rowE !mxE !big_ord1 !mxE !eqxx !mulr_natl /= andbT eq_sym.
Qed.

Lemma mx_abs_irred_irr : mx_absolutely_irreducible -> mx_irreducible.
Proof.
case/mx_abs_irrP=> n_gt0 [a_ a_G]; apply/mx_irrP; split=> // U Umod.
case/rowV0Pn=> u Uu; rewrite -mxrank_eq0 -lt0n row_leq_rank -subset1mx.
case/subsetmxP: Uu => v ->{u}; case/row_freeP=> u' vK; apply/row_subP=> i.
rewrite rowE scalar_mxC -{}vK -2!mulmxA; move: {u' i}(u' *m _) => A.
rewrite subsetmxMtrans {v}// [A]a_G linear_sum subsetmx_sum //= => x Gx.
by rewrite linearZ /= subsetmx_scale // (submodmxP _ Umod).
Qed.

Lemma decide_mx_Jacobson_density :
  (cent_mx (cent_mx E_G) <= E_G)%MR + mx_reducible.
Proof.
have Emod: forall x, x \in G -> (E_G *m lin_mx (mulmxr (rG x)) <= E_G)%MR.
  move=> x Gx; apply/row_subP=> i; rewrite row_mul mul_rV_lin /=.
  case: (row_envelopE i) => y Gy ->{i}; rewrite mxvecK -repr_mxM //.
  by case: (row_envelopI (groupM Gy Gx)) => i ->; rewrite vec_mxK row_sub.
pose pB (I : {set 'I_n}) : 'M[F]_n := \sum_(i \in I) delta_mx i i.
pose pK I := kermx (lin_mx (mulmx (pB I)) : 'M_(n * n)).
have pKmod: forall I A, (pK I *m lin_mx (mulmxr A) <= pK I)%MR.
  move=> I A; apply/row_subP=> i; rewrite row_mul mul_rV_lin /=.
  apply/subsetmx_kerP; move/subsetmx_kerP: (row_sub i (pK I)).
  rewrite mul_vec_lin /= mulmxA mul_rV_lin /=; move/(canRL mxvecK) => ->.
  by rewrite !(linear0, mul0mx).
pose pE' I := \rank (E_G :&: pK I)%MR <= 0.
have: exists I, pE' I; last do [case/ex_minset=> I; case/minsetP=> pE'_I Imin].
  exists setT; apply: leq_trans (mxrankS (capmxSr _ _)) _ => /=.
  rewrite mxrank_ker (_ : lin_mx _ = 1%:M) ?mxrank1 ?subnn //.
  apply/row_matrixP=> u; rewrite rowE mul_rV_lin row1 /=.
  by rewrite [pB _](eq_bigl _ _ (@in_setT _)) -mx1_sum_delta mul1mx vec_mxK.
case sub1EI: (1%:M <= E_G :+: pK I)%MR; [left | right=> _].
  move: sub1EI; rewrite eqmx_gsum; case/subsetmxP=> EI'.
  rewrite -[EI']hsubmxK mul_row_col; move/(canLR (addrK _)).
  set E' := _ - _ => defE'.
  apply/row_subP=> iB; rewrite -[row iB _]vec_mxK; set B := vec_mx _.
  have cBcE: forall A, centgmx A -> A *m B = B *m A.
    move=> A; rewrite -subsetmx_cent_envelop -{-1}[A]mxvecK.
    case/subsetmxP=> u ->{A}.
    rewrite [u]matrix_sum_delta big_ord1 !(mulmx_suml, linear_sum) /=.
    apply: eq_bigr => i _; rewrite -scalemxAl !linearZ -scalemxAl /= -rowE.
    by congr (_ *m: _); apply: subset_cent_rowP i; rewrite vec_mxK row_sub.
  pose fE' i j : 'rV_n -> 'rV_n :=
    row j \o vec_mx \o mulmxr E' \o mxvec \o mulmx (delta_mx i 0).
  have cBfE': forall i j, lin1_mx (fE' i j) *m B = B *m lin1_mx (fE' i j).
    move=> i j; apply: cBcE; apply/centgmxP=> x Gx; apply/row_matrixP=> k.
    symmetry; rewrite !rowE !mulmxA !mul_rV_lin1 /= -row_mul mulmxA.
    congr row; move: {i j k}(delta_mx i 0 *m _) => A; apply: (canLR mxvecK).
    rewrite -!(mul_vec_lin (mulmxr_linear _ _)) /= vec_mxK -!mulmxA.
    congr (_ *m _) => {A}; apply/eqP; rewrite -subr_eq0 -mxrank_eq0 -leqn0.
    rewrite (leq_trans _ pE'_I) // mxrankS // sub_capmx.
    rewrite {1 2}defE' mulmx_subl mul1mx oppr_sub addrCA mulmx_subr mulmx1.
    rewrite !addrA addrAC addrK 2!mulmxA -!mulNmx.
    by rewrite !subsetmx_add ?subsetmxMl // -mulmxA subsetmxMtrans ?Emod.
  rewrite -[B]mul1mx -repr_mx1 -(mul_vec_lin (mulmxr_linear _ _)).
  set A := mxvec _; have ->: A = A *m E'.
    apply/eqP; rewrite -subr_eq0 -mxrank_eq0 -leqn0 (leq_trans _ pE'_I) //.
    rewrite mxrankS  // sub_capmx.
    rewrite {1}defE' mulmx_addr mulmx1 oppr_add addNKr mulmxN opprK 2!mulmxA.
    rewrite -mulNmx !subsetmx_add ?subsetmxMl // /A.
    by case/row_envelopI: (group1 G) => i ->; rewrite vec_mxK row_sub.
  suffices ->: A *m E' *m lin_mx (mulmxr B) = A *m lin_mx (mulmxr B) *m E'.
    by rewrite defE' !mulmxA subsetmxMl.
  rewrite {}/A repr_mx1 mx1_sum_delta linear_sum !mulmx_suml.
  apply: eq_bigr => i _.
  rewrite -(mul_delta_mx (0 : 'I_1)) mul_vec_lin mul_rV_lin /=.
  apply: (canLR vec_mxK); apply/row_matrixP=> j; rewrite -(mulmxA _ _ B).
  rewrite row_mul -![row j _](mul_rV_lin1 [linear of fE' i j]).
  by rewrite -!mulmxA cBfE'.
case/row_subPn: sub1EI; case/mxvec_indexP=> i0 j0; rewrite row1 -mxvec_delta.
set u := mxvec _ => nEIu; pose W := (E_G :&: pK (I :\ i0))%MR.
have Ii0: i0 \in I.
  apply: contraR nEIu => nIi0; apply: subsetmx_trans (gsummxSr _ _).
  apply/subsetmx_kerP; rewrite mul_vec_lin /= mulmx_suml big1 ?linear0 //.
  by move=> i Ii; rewrite mul_delta_mx_cond; case: eqP Ii nIi0 => // -> ->.
pose fU : 'rV[F]_(n * n) -> 'rV_n := row i0 \o vec_mx.
pose U := W *m lin1_mx fU; exists <<U>>%MR; rewrite eqmx_gen; apply/andP; split.
  apply/submodmxP=> x Gx; rewrite eqmx_gen (eqmxMr _ (eqmx_gen U)).
  apply/row_subP=> iG; rewrite 2!row_mul mul_rV_lin1 /= !rowE.
  rewrite -mulmxA -[_ *m rG x](mx_rV_lin (mulmxr_linear _ _)) /=.
  have: (W *m lin_mx (mulmxr (rG x)) <= W)%MR.
    by apply: subsetmx_trans (capmxMr _ _ _) (capmxS _ _); rewrite ?Emod.
  rewrite -mulmxA; case/subsetmxP=> w ->; rewrite mulmxA -!rowE.
  by rewrite -[row _ _](mul_rV_lin1 [linear of fU]) -mulmxA subsetmxMl.
apply/andP; split.
  case: (eqVneq W 0) => [W0 |].
    suffices: #|I| <= #|I :\ i0| by rewrite (cardsD1 i0) Ii0 ltnn.
    by rewrite (Imin _ _ (subsetDl _ _)) /pE' -/W ?W0 ?mxrank0.
  rewrite -mxrank_eq0 -leqn0 lt0n mxrank_eq0; apply: contra; move/eqP=> U0.
  rewrite (leq_trans _ pE'_I) ?mxrankS ?sub_capmx ?capmxSl //=.
  apply/row_subP=> k; apply/subsetmx_kerP.
  rewrite mul_rV_lin /= [pB I](big_setD1 i0) //= -/(pB _).
  rewrite mulmx_addl -(mul_delta_mx (0 : 'I_1)) -mulmxA -rowE.
  rewrite -[row i0 _](mul_rV_lin1 [linear of fU]) -row_mul -/U U0 !linear0.
  rewrite add0r -mul_rV_lin; apply/subsetmx_kerP; rewrite -/(pK _).
  by rewrite rowE subsetmxMtrans ?capmxSr.
rewrite ltnNge col_leq_rank; apply: contra nEIu; case/row_fullP=> U' U'U1.
set v : 'rV_(n * n) := delta_mx 0 j0 *m U' *m W.
have ->: u = row_mx 1 1 *m col_mx v (u - v).
  by rewrite mul_row_col !mul1mx addrC subrK.
rewrite subsetmxMtrans // -eqmx_gsum gsummxS //.
  by rewrite !(capmxSl, subsetmxMtrans).
apply/subsetmx_kerP; rewrite mul_rV_lin //= [pB _](big_setD1 i0) //= -/(pB _).
apply: (canLR vec_mxK); rewrite mulmx_addl linear0 !linearD !linearN /=.
rewrite -{2}(mul_delta_mx (0 : 'I_1)) -mulmxA -rowE.
rewrite -[row _ _](mul_rV_lin1 [linear of fU]) -2!mulmxA U'U1 mulmx1.
rewrite mxvecK !mul_delta_mx subrr add0r mulmx_suml big1 ?add0r => [|i'].
  rewrite -mx_rV_lin (subsetmx_kerP _ _ _) ?linear0 // -/(pK _).
  by rewrite subsetmxMtrans // capmxSr.
by case/setD1P=> ne_i'i _; rewrite mul_delta_mx_0.
Qed.

Lemma mx_Jacobson_density : mx_irreducible -> (cent_mx (cent_mx E_G) <= E_G)%MR.
Proof. by case decide_mx_Jacobson_density. Qed.

Lemma cent_mx_scalar_abs_irr :
  mx_irreducible -> \rank (cent_mx E_G) <= 1 -> mx_absolutely_irreducible.
Proof.
set C := cent_mx _ => irrG; have:= has_non_scalar_mxP C.
rewrite (leqNgt _ 1) scalar_mx_cent /= => [[//|scalC _]].
apply/andP; split; first by case/mx_irrP: irrG.
rewrite [_ E_G]eqn_leq rank_leq_col -{1}(mxrank1 F (n * n)) mxrankS //.
apply: subsetmx_trans (mx_Jacobson_density irrG); rewrite -/C.
apply/row_subP; case/mxvec_indexP=> i j; rewrite row1 -mxvec_delta.
apply/subset_cent_mxP=> A sAC.
case scalA: (is_scalar_mx A); last by case: scalC; exists A; rewrite ?scalA.
by case/is_scalar_mxP: scalA => a ->; rewrite mul_scalar_mx mul_mx_scalar.
Qed.

End Representation.

Section SubGroup.

Variables (gT : finGroupType) (G H : {group gT}) (n : nat).
Variables (rG : mx_representation G n) (sHG : H \subset G).

Lemma subg_mx_repr : mx_repr H rG.
Proof.
by split=> [|x y Hx Hy]; rewrite (repr_mx1, repr_mxM) ?(subsetP sHG).
Qed.
Definition subg_repr := MxRepresentation subg_mx_repr.

Lemma rfix_subg : (rfix_mx rG <= rfix_mx subg_repr)%MR.
Proof.
apply/row_subP=> i; apply/subsetmx_rfixP => /= x; move/(subsetP sHG); move: x.
by apply/subsetmx_rfixP; exact: row_sub.
Qed.

Lemma rcent_subg : forall U, rcent subg_repr U = H :&: rcent rG U.
Proof.
by move=> U; apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG).
Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstab_subg : rstab subg_repr U = H :&: rstab rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

Lemma rstabs_subg : rstabs subg_repr U = H :&: rstabs rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

End Stabilisers.

Lemma rker_subg : rker subg_repr = H :&: rker rG. Proof. exact: rstab_subg. Qed.

Lemma subg_repr_faithful : mx_repr_faithful rG -> mx_repr_faithful subg_repr.
Proof. by apply: subset_trans; rewrite rker_subg subsetIr. Qed.

End SubGroup.

Section Submodule.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation G n) (U : 'M[F]_n) (Umod : submodmx rG U).
Local Notation rU := (submod_repr Umod).
Local Notation rU' := (factmod_repr Umod).

Lemma rfix_submod : (rfix_mx rU :=: in_submod U (U :&: rfix_mx rG))%MR.
Proof.
apply/eqmxP; apply/andP; split.
  rewrite -[rfix_mx _]val_submodK subsetmxMr // sub_capmx val_submodP.
  apply/subsetmx_rfixP=> x Gx; rewrite -(val_submodJ Umod) //.
  by rewrite (subsetmx_rfixP _ _ (subsetmx_refl _)).
apply/subsetmx_rfixP=> x Gx; rewrite -in_submodJ ?capmxSl //.
by rewrite (subsetmx_rfixP rG _ _) ?capmxSr.
Qed.

Lemma rfix_factmod_mx : (in_factmod U (rfix_mx rG) <= rfix_mx rU')%MR.
Proof.
apply/subsetmx_rfixP=> x Gx; rewrite -(in_factmodJ Umod) //.
by rewrite (subsetmx_rfixP rG _ _).
Qed.

Lemma rstab_submod : forall m (W : 'M_(m, \rank U)),
  rstab rU W = rstab rG (val_submod W).
Proof.
move=> m W; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
by rewrite -(inj_eq (@val_submod_inj _ _ _)) val_submodJ.
Qed.

Lemma rstabs_submod : forall m (W : 'M_(m, \rank U)),
  rstabs rU W = rstabs rG (val_submod W).
Proof.
move=> m W; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
by rewrite -val_submodS val_submodJ.
Qed.

Lemma rstab_factmod : forall m (W : 'M_(m, n)),
  rstab rG W \subset rstab rU' (in_factmod U W).
Proof.
move=> m  W; apply/subsetP=> x; case/setIdP=> Gx; move/eqP=> cUW.
by rewrite inE Gx -in_factmodJ //= cUW.
Qed.

Lemma rstabs_factmod : forall m (W : 'M_(m, \rank (cokermx U))),
  rstabs rU' W = rstabs rG (U :+: val_factmod W)%MR.
Proof.
move=> m W; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
rewrite gsummxMr gsummx_sub (subsetmx_trans _ (gsummxSl _ _)) /=; last first.
  by move/submodmxP: Umod; apply.
rewrite -[_ *m rG x](sum_sub_fact_mod U) -val_factmodS val_factmodJ //.
apply/idP/idP=> nWx.
  rewrite subsetmx_add // ?(subsetmx_trans nWx) ?gsummxSr //.
  by rewrite (subsetmx_trans _ (gsummxSl _ _)) ?val_submodP.
case/sub_gsummxP: nWx => W'; set U' := val_submod _; set W'' := val_factmod _.
move=> sU'U sW'W; suff: W'' == W' by move/eqP->.
rewrite -subr_eq0 -subsetmx0 -(capmx_compl U) sub_capmx andbC.
rewrite subsetmx_add ?eqmx_opp ?(subsetmx_trans sW'W) ?val_factmodP //.
by rewrite -[_ - _](addKr U') (addrA U') subsetmx_add ?eqmx_opp ?val_submodP.
Qed.

Lemma rker_submod : rker rG \subset rker rU.
Proof.
apply/subsetP=> x; case/rkerP=> Gx cVx.
by rewrite !inE Gx /= /submod_mx cVx mul1mx scalar_mxC val_submodK.
Qed.

Lemma submod_repr_faithful : mx_repr_faithful rU -> mx_repr_faithful rG.
Proof. exact: subset_trans rker_submod. Qed.

Lemma rker_factmod : rker rG \subset rker rU'.
Proof.
apply/subsetP=> x; case/rkerP=> Gx cVx.
by rewrite inE Gx /= /factmod_mx cVx mul1mx mulmx1 val_factmodK.
Qed.

Lemma factmod_repr_faithful : mx_repr_faithful rU' -> mx_repr_faithful rG.
Proof. exact: subset_trans rker_factmod. Qed.

End Submodule.

Section Compose.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Variables (G : {group rT}) (n : nat) (rG : mx_representation G n).

Lemma comp_mx_repr : mx_repr (f @*^-1 G) (rG \o f).
Proof.
split=> [|x y]; first by rewrite /= morph1 repr_mx1.
case/morphpreP=> Dx Gfx; case/morphpreP=> Dy Gfy.
by rewrite /= morphM ?repr_mxM.
Qed.
Canonical Structure comp_repr := MxRepresentation comp_mx_repr.
Local Notation rGf := comp_repr.

Lemma rstab_comp : forall m (U : 'M_(m, n)),
  rstab rGf U = f @*^-1 (rstab rG U).
Proof. by move=> m U; apply/setP=> x; rewrite !inE andbA. Qed.

Lemma rstabs_comp : forall m (U : 'M_(m, n)),
  rstabs rGf U = f @*^-1 (rstabs rG U).
Proof. by move=> m U; apply/setP=> x; rewrite !inE andbA. Qed.

Lemma rker_comp : rker rGf = f @*^-1 (rker rG).
Proof. exact: rstab_comp. Qed.

Lemma submodmx_comp : G \subset f @* D -> submodmx rGf =1 submodmx rG.
Proof. by move=> sGf U; rewrite /submodmx rstabs_comp morphpreSK. Qed.

Lemma comp_mx_irr :
  G \subset f @* D -> (mx_irreducible rGf <-> mx_irreducible rG).
Proof.
move/submodmx_comp=> modG; split=> irrG redG;
  by case: irrG; case/redG=> // U redU; exists U; rewrite modG in redU *.
Qed.

End Compose.

Section Conjugate.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation G n) (B : 'M[F]_n).

Definition rconj_mx of B \in unitmx := fun x => B *m rG x *m invmx B.

Hypothesis uB : B \in unitmx.

Lemma rconj_mx_repr : mx_repr G (rconj_mx uB).
Proof.
split=> [|x y Gx Gy]; rewrite /rconj_mx ?repr_mx1 ?mulmx1 ?mulmxV ?repr_mxM //.
by rewrite !mulmxA mulmxKV.
Qed.
Canonical Structure rconj_repr := MxRepresentation rconj_mx_repr.
Local Notation rGB := rconj_repr.

Lemma rconj_mxE : forall x, rGB x = B *m rG x *m invmx B.
Proof. by []. Qed.

Lemma rconj_mxJ : forall m (W : 'M_(m, n)) x, W *m rGB x *m B = W *m B *m rG x.
Proof. by move=> m W x; rewrite !mulmxA mulmxKV. Qed.

Lemma rfix_conj : (rfix_mx rGB :=: B *m rfix_mx rG *m invmx B)%MR.
Proof.
apply/eqmxP; apply/andP; split.
  rewrite -mulmxA (eqmxMfull (_ *m _)) ?row_full_unit //.
  rewrite -[rfix_mx rGB](mulmxK uB) subsetmxMr //; apply/subsetmx_rfixP=> x Gx.
  apply: (canRL (mulmxKV uB)); rewrite -rconj_mxJ mulmxK //.
  by move: x Gx; exact/subsetmx_rfixP.
apply/subsetmx_rfixP=> x Gx; rewrite -3!mulmxA; congr (_ *m _).
by rewrite !mulmxA mulmxKV //; congr (_ *m _); move: x Gx; exact/subsetmx_rfixP.
Qed.

Lemma rcent_conj : forall A, rcent rGB A = rcent rG (invmx B *m A *m B).
Proof.
move=> A; apply/setP=> x; rewrite !inE /= rconj_mxE !mulmxA.
rewrite (can2_eq (mulmxKV uB) (mulmxK uB)) -!mulmxA.
by rewrite -(can2_eq (mulKVmx uB) (mulKmx uB)).
Qed.

Lemma rstab_conj : forall m (U : 'M_(m, n)), rstab rGB U = rstab rG (U *m B).
Proof.
move=> m U; apply/setP=> x; rewrite !inE /= rconj_mxE !mulmxA.
by rewrite (can2_eq (mulmxKV uB) (mulmxK uB)).
Qed.

Lemma rstabs_conj : forall m (U : 'M_(m, n)), rstabs rGB U = rstabs rG (U *m B).
Proof.
move=> m U; apply/setP=> x; rewrite !inE rconj_mxE !mulmxA.
by rewrite -{2}[U](mulmxK uB) subsetmxMfree // row_free_unit unitmx_inv.
Qed.

Lemma submodmx_conj : forall U, submodmx rGB U = submodmx rG (U *m B).
Proof. by move=> U; rewrite /submodmx rstabs_conj. Qed.

Lemma rker_conj : rker rGB = rker rG.
Proof.
apply/setP=> x; rewrite !inE /= mulmxA (can2_eq (mulmxKV uB) (mulmxK uB)).
by rewrite mul1mx -scalar_mxC (inj_eq (can_inj (mulKmx uB))) mul1mx.
Qed.

Lemma conj_repr_faithful : mx_repr_faithful rGB = mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_conj. Qed.

Lemma conj_mx_irr : mx_irreducible rGB <-> mx_irreducible rG.
Proof.
split=> irrG redG; case: irrG; case/redG=> U Urmod.
  exists (U *m invmx B); rewrite submodmx_conj mulmxKV // mxrankMfree //.
  by rewrite row_free_unit unitmx_inv.
by exists (U *m B); rewrite -submodmx_conj mxrankMfree // row_free_unit.
Qed.

End Conjugate.

Section Quotient.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation G n.

Definition quo_mx (H : {set gT}) of H \subset rker rG & G \subset 'N(H) :=
  fun Hx : coset_of H => rG (repr Hx).

Section SubQuotient.

Variable H : {group gT}.
Hypotheses (krH : H \subset rker rG) (nHG : G \subset 'N(H)).
Let nHGs := subsetP nHG.

Let quo_mx_coset : forall x, x \in G -> quo_mx krH nHG (coset H x) = rG x.
Proof.
move=> x Gx; rewrite /quo_mx val_coset ?nHGs //; case: repr_rcosetP => z Hz.
by case/rkerP: (subsetP krH z Hz) => Gz rz1; rewrite repr_mxM // rz1 mul1mx.
Qed.

Lemma quo_mx_repr : mx_repr (G / H)%g (quo_mx krH nHG).
Proof.
split=> [|Hx Hy]; first by rewrite /quo_mx repr_coset1 repr_mx1.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM // !quo_mx_coset ?groupM ?repr_mxM.
Qed.
Canonical Structure quo_repr := MxRepresentation quo_mx_repr.
Local Notation rGH := quo_repr.

Lemma quo_repr_coset : forall x, x \in G -> rGH (coset H x) = rG x.
Proof. exact: quo_mx_coset. Qed.

Lemma quo_mx_quotient :
  (enveloping_algebra_mx rGH :=: enveloping_algebra_mx rG)%MR.
Proof.
apply/eqmxP; apply/andP; split; apply/row_subP=> i.
  case: (row_envelopE rGH i) => Hx; case/morphimP=> x _ Gx ->{Hx} ->{i}.
  rewrite quo_repr_coset //; case: (row_envelopI rG Gx) => i ->.
  by rewrite vec_mxK row_sub.
case: (row_envelopE rG i) => x Gx ->{i}; rewrite -quo_mx_coset //.
have: coset H x \in (G / H)%g by rewrite mem_quotient.
by case/(row_envelopI rGH) => i ->; rewrite vec_mxK row_sub.
Qed.

Lemma rfix_quo : (rfix_mx rGH :=: rfix_mx rG)%MR.
Proof.
apply/eqmxP; apply/andP; (split; apply/subsetmx_rfixP) => [x Gx | Hx].
  rewrite -quo_mx_coset //.
  by rewrite (subsetmx_rfixP _ _ (subsetmx_refl _)) ?mem_quotient.
by case/morphimP=> x Nx Gx ->; rewrite quo_repr_coset ?(subsetmx_rfixP rG _ _).
Qed.

Lemma rcent_quo : forall A, rcent rGH A = (rcent rG A / H)%g.
Proof.
move=> A; apply/setP=> Hx; rewrite !inE.
apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => cAx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx cAx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma rstab_quo : forall m (U : 'M_(m, n)), rstab rGH U = (rstab rG U / H)%g.
Proof.
move=> m U; apply/setP=> Hx; rewrite !inE.
apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => nUx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx nUx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma rstabs_quo : forall m (U : 'M_(m, n)), rstabs rGH U = (rstabs rG U / H)%g.
Proof.
move=> m U; apply/setP=> Hx; rewrite !inE.
apply/andP/idP=> [[]|]; case/morphimP=> x Nx Gx ->{Hx}.
  by rewrite quo_repr_coset // => nUx; rewrite mem_morphim // inE Gx.
by case/setIdP: Gx => Gx nUx; rewrite quo_repr_coset ?mem_morphim.
Qed.

Lemma submodmx_quo : submodmx rGH =1 submodmx rG.
Proof.
move=> U; rewrite /submodmx rstabs_quo quotientSGK // ?(subset_trans krH) //.
apply/subsetP=> x; rewrite !inE mul1mx; case/andP=> ->; move/eqP->.
by rewrite /= mulmx1.
Qed.

Lemma quo_mx_irr : mx_irreducible rGH <-> mx_irreducible rG.
Proof.
split=> irrG redG; case: irrG; case/redG=> // U redU;
  by exists U; rewrite submodmx_quo in redU *.
Qed.

Lemma rker_quo : rker rGH = (rker rG / H)%g.
Proof. exact: rstab_quo. Qed.

End SubQuotient.

Definition kquo_mx := quo_mx (subxx (rker rG)) (rker_norm rG).
Lemma kquo_mxE : kquo_mx = quo_mx (subxx (rker rG)) (rker_norm rG).
Proof. by []. Qed.

Canonical Structure kquo_repr :=
  @MxRepresentation _ _ _ kquo_mx (quo_mx_repr _ _).

Lemma kquo_repr_coset : forall x,
  x \in G -> kquo_repr (coset (rker rG) x) = rG x.
Proof. exact: quo_repr_coset. Qed.

Lemma kquo_mx_faithful : mx_repr_faithful kquo_repr.
Proof. by rewrite /mx_repr_faithful rker_quo trivg_quotient. Qed.

End Quotient.

Section Proper.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable rG : mx_representation G n.

Lemma repr_mxMr : {in G &, {morph rG : x y / (x * y)%g >-> x * y}}.
Proof. exact: repr_mxM. Qed.

Lemma repr_mxVr : {in G, {morph rG : x / (x^-1)%g >-> x^-1}}.
Proof. exact: repr_mxV.
 Qed.

Lemma repr_mx_unitr : forall x, x \in G -> GRing.unit (rG x).
Proof. exact: repr_mx_unit. Qed.

Lemma repr_mxX : forall m, {in G, {morph rG : x / (x ^+ m)%g >-> x ^+ m}}.
Proof.
elim=> [|m IHm] x Gx; rewrite /= ?repr_mx1 // expgS exprS -IHm //.
by rewrite repr_mxM ?groupX.
Qed.

Lemma mx_repr_faithful_irr_abelian_cyclic :
  mx_irreducible rG -> mx_repr_faithful rG -> abelian G -> cyclic G.
Proof.
move=> irrG; move/trivgP=> KrG1 abelG.
apply: (div_ring_mul_group_cyclic (repr_mx1 rG)) (repr_mxM rG) _ _ => // x.
rewrite -[[set _]]KrG1 !inE mul1mx -subr_eq0 andbC; set U := _ - _.
case/andP=> Gx; rewrite Gx /=; move/eqP; case/(mx_Schur irrG): (U) => //.
apply/centgmxP=> y Gy; rewrite mulmx_subl mulmx_subr mulmx1 mul1mx.
by rewrite -!repr_mxM // (centsP abelG).
Qed.

End Proper.

End GenRepr.

(* This is Gorenstein, Lemma 2.6.3. *)
Lemma rfix_pgroup_char : forall (F : fieldType) (gT : finGroupType),
    forall (G : {group gT}) n (rG : mx_representation F G n),
  n > 0 -> [char F].-group G -> rfix_mx rG != 0.
Proof.
move=> F gT G n; move: {2}_.+1 (ltnSn (n + #|G|)) => m.
elim: m => // m IHm in gT n G *; rewrite ltnS => le_nG_m rG n_gt0 charF_G.
apply/eqP=> Gregular; have irrG: mx_irreducible rG.
  case=> // U; case/and3P=> Umod Unz ltUn.
  have: rfix_mx (submod_repr Umod) != 0.
    by apply: IHm => //; apply: leq_trans le_nG_m; rewrite ltn_add2r.
  by rewrite -mxrank_eq0 (rfix_submod Umod) // Gregular capmx0 linear0 mxrank0.
have{m le_nG_m IHm} faithfulG: mx_repr_faithful rG.
  apply/trivgP; apply/eqP; apply/idPn; set C := _ rG => ntC.
  suffices: rfix_mx (kquo_repr rG) != 0.
    by rewrite -mxrank_eq0 rfix_quo Gregular mxrank0.
  apply: IHm (morphim_pgroup _ _) => //.
  by apply: leq_trans le_nG_m; rewrite ltn_add2l ltn_quotient // rstab_sub.
have{Gregular} ntG: G :!=: 1%g.
  apply: contraL n_gt0; move/eqP=> G1; rewrite -leqNgt -(mxrank1 F n).
  rewrite -(mxrank0 F n n) -Gregular mxrankS //; apply/subsetmx_rfixP=> x.
  by rewrite {1}G1 mul1mx; move/set1P->; rewrite repr_mx1.
have [p p_pr charFp]: exists2 p, prime p & p \in [char F].
  move: ntG; rewrite trivg_card_le1 -ltnNge; case/pdivP=> p p_pr pG.
  by exists p => //; exact: pgroupP pG.
have{charF_G} pG: p.-group G by rewrite /pgroup -(eq_pnat _ (charf_eq charFp)).
have{ntG pG} [z]: {z | z \in 'Z(G) & #[z] = p}; last case/setIP=> Gz cGz ozp.
  apply: Cauchy => //; apply: contraR ntG; rewrite -p'natE // => p'Z.
  have pZ: p.-group 'Z(G) by rewrite (pgroupS (center_sub G)).
  by rewrite (trivg_center_pgroup pG (card1_trivg (pnat_1 pZ p'Z))).
have{cGz} cGz1: centgmx rG (rG z - 1%:M).
  apply/centgmxP=> x Gx; rewrite mulmx_subl mulmx_subr mulmx1 mul1mx.
  by rewrite -!repr_mxM // (centP cGz).
case/mx_Schur: cGz1 => {irrG}// [rz1 | Urz1 {faithfulG}].
  move/implyP: (subsetP faithfulG z); rewrite !inE mul1mx Gz -subr_eq0 rz1 eqxx.
  by move/eqP=> z1; rewrite -ozp z1 order1 in p_pr.
do [case: n n_gt0 => // n' _; set n := n'.+1] in rG Urz1 *.
have{charFp} charMp: p \in [char 'M[F]_n] by rewrite (fieldM_char scalar_mxRM).
have{Urz1}: GRing.unit (Frobenius_aut charMp (rG z - 1)) by rewrite unitr_exp.
rewrite (Frobenius_aut_sub_comm _ (commr1 _)) Frobenius_aut_1.
by rewrite -[_ (rG z)](repr_mxX rG) // -ozp expg_order repr_mx1 subrr unitr0.
Qed.

(* Lifting term, formula, envs and eval to matrices. Wlog, and for the sake  *)
(* of simplicity, we only lift (tensor) envs to row vectors; we can always   *)
(* use mxvec/vec_mx to store and retrieve matrices.                          *)
(* We don't provide definitions for addition, substraction, scaling, etc,    *)
(* because they have simple matrix expressions.                              *)
Module MatrixFormula.

Section MatrixFormula.

Variable F : decFieldType.

Local Notation False := GRing.False.
Local Notation True := GRing.True.
Local Notation And := GRing.And (only parsing).
Local Notation Add := GRing.Add (only parsing).
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).
Local Notation eval := GRing.eval.
Local Notation holds := GRing.holds.
Local Notation qf_form := GRing.qf_form.
Local Notation qf_eval := GRing.qf_eval.

Definition eval_mx (e : seq F) := map_mx (eval e).

Definition mx_term := map_mx (@GRing.Const F).

Lemma eval_mx_term : forall e m n (A : 'M_(m, n)), eval_mx e (mx_term A) = A.
Proof. by move=> e m n A; apply/matrixP=> i j; rewrite !mxE. Qed.

Definition mulmx_term m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)) :=
  \matrix_(i, k) (\big[Add/0]_j (A i j * B j k))%T.

Lemma eval_mulmx : forall e m n p (A : 'M[term]_(m, n)) (B : 'M_(n, p)),
  eval_mx e (mulmx_term A B) = eval_mx e A *m eval_mx e B.
Proof.
move=> e m n p A B; apply/matrixP=> i k; rewrite !mxE /=.
rewrite (@big_morph _ _ _ 0 _ +%R (eval e)) //=.
by apply: eq_bigr => j _; rewrite /= !mxE.
Qed.

Local Notation morphAnd := (@big_morph _ _ _ true _ andb).

Let Schur m n (A : 'M[term]_(1 + m, 1 + n)) (a := A 0 0) :=
  \matrix_(i, j) (drsubmx A i j - a^-1 * dlsubmx A i 0%R * ursubmx A 0%R j)%T.

Fixpoint mxrank_form (r m n : nat) : 'M_(m, n) -> form :=
  match m, n return 'M_(m, n) -> form with
  | m'.+1, n'.+1 => fun A : 'M_(1 + m', 1 + n') =>
    let nzA k := A k.1 k.2 != 0 in
    let xSchur k := Schur (xrow k.1 0%R (xcol k.2 0%R A)) in
    let recf k := Bool (r > 0) /\ mxrank_form r.-1 (xSchur k) in
    GRing.Pick nzA recf (Bool (r == 0%N))
  | _, _ => fun _ => Bool (r == 0%N)
  end%T.

Lemma mxrank_form_qf : forall r m n (A : 'M_(m, n)), qf_form (mxrank_form r A).
Proof.
move=> r m; elim: m r => [|m IHm] r [|n] A //=.
by rewrite GRing.Pick_form_qf /=.
Qed.

Lemma eval_mxrank : forall e r m n (A : 'M_(m, n)),
  qf_eval e (mxrank_form r A) = (\rank (eval_mx e A) == r).
Proof.
move=> e r m; elim: m r => [|m IHm] r [|n] A /=; try by case r.
rewrite GRing.eval_Pick /mxrank /=; set pf := fun _ => _.
rewrite -(@eq_pick _ pf) => [|k]; rewrite {}/pf ?mxE // eq_sym.
case: pick => [[i j]|] //=; set B := _ - _; have: \rank B = (emxrank B).2 by [].
case: emxrank r => [[_ _] _] [|r] //= <-; rewrite {}IHm; congr (\rank _ == r).
by apply/matrixP=> i' j'; rewrite !(mxE, big_ord1) !tpermR.
Qed.

Lemma eval_vec_mx : forall e m n (u : 'rV_(m * n)),
  eval_mx e (vec_mx u) = vec_mx (eval_mx e u).
Proof. by move=> e m n u; apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma eval_mxvec : forall e m n (A : 'M_(m, n)),
  eval_mx e (mxvec A) = mxvec (eval_mx e A).
Proof. by move=> e m n A; rewrite -{2}[A]mxvecK eval_vec_mx vec_mxK. Qed.

Section Subsetmx.

Variables (m1 m2 n : nat) (A : 'M[term]_(m1, n)) (B : 'M[term]_(m2, n)).

Definition subsetmx_form :=
  \big[And/True]_(r < n.+1) (mxrank_form r (col_mx A B) ==> mxrank_form r B)%T.

Lemma eval_col_mx : forall e,
  eval_mx e (col_mx A B) = col_mx (eval_mx e A) (eval_mx e B).
Proof.
by move=> e; apply/matrixP=> i j; do 2![rewrite !mxE //; case: split => ?].
Qed.

Lemma subsetmx_form_qf : qf_form subsetmx_form.
Proof.
by rewrite (morphAnd (@qf_form _)) ?big1 //= => r _; rewrite !mxrank_form_qf.
Qed.

Lemma eval_subsetmx : forall e,
  qf_eval e subsetmx_form = (eval_mx e A <= eval_mx e B)%MR.
Proof.
move=> e; rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/idP=> [|sAB d]; last first.
  rewrite !eval_mxrank eval_col_mx -eqmx_gsum; apply/implyP; move/eqP <-.
  by rewrite mxrank_leqif_sup ?gsummxSr // gsummx_sub sAB /=.
move/(_ (inord (\rank (eval_mx e (col_mx A B))))).
rewrite inordK ?ltnS ?rank_leq_col // !eval_mxrank eqxx /= eval_col_mx.
by rewrite -eqmx_gsum mxrank_leqif_sup ?gsummxSr // gsummx_sub; case/andP.
Qed.

End Subsetmx.

Section Env.

Variable d : nat.

Definition seq_of_rV (v : 'rV_d) : seq F := fgraph [ffun i => v 0 i].

Lemma size_seq_of_rV : forall v, size (seq_of_rV v) = d.
Proof. by move=> v; rewrite tuple.size_tuple card_ord. Qed.

Lemma nth_seq_of_rV : forall x0 v (i : 'I_d), nth x0 (seq_of_rV v) i = v 0 i.
Proof. by move=> x0 v i; rewrite nth_fgraph_ord ffunE. Qed.

Definition row_var k : 'rV[term]_d := \row_i ('X_(k * d + i))%T.

Definition row_env (e : seq 'rV_d) := flatten (map seq_of_rV e).

Lemma nth_row_env : forall e k (i : 'I_d), (row_env e)`_(k * d + i) = e`_k 0 i.
Proof.
move=> e k i; elim: e k => [|v e IHe] k; first by rewrite !nth_nil mxE.
rewrite /row_env /= nth_cat size_seq_of_rV.
case: k => [|k]; first by rewrite (valP i) nth_seq_of_rV.
by rewrite mulSn -addnA -if_neg -leqNgt leq_addr addKn IHe.
Qed.

Lemma eval_row_var : forall e k,
  eval_mx (row_env e) (row_var k) = e`_k :> 'rV_d.
Proof. by move=> e k; apply/rowP=> i; rewrite !mxE /= nth_row_env. Qed.

Definition Exists_row_form k (f : form) :=
  foldr GRing.Exists f (map (fun i : 'I_d => k * d + i)%N (enum 'I_d)).

Lemma Exists_rowP : forall e k f,
  d > 0 ->
   ((exists v : 'rV[F]_d, holds (row_env (set_nth 0 e k v)) f)
      <-> holds (row_env e) (Exists_row_form k f)).
Proof.
move=> e k f d_gt0; pose i_ j := Ordinal (ltn_pmod j d_gt0).
have d_eq : forall j, (j = j %/ d * d + i_ j)%N := divn_eq^~ d.
split=> [[v f_v] | ]; last case/GRing.foldExistsP=> e' ee' f_e'.
  apply/GRing.foldExistsP; exists (row_env (set_nth 0 e k v)) => {f f_v}// j.
  rewrite [j]d_eq !nth_row_env nth_set_nth /=; case: eqP => // ->.
  by case/mapP; exists (i_ j); rewrite ?mem_enum.
exists (\row_i e'`_(k * d + i)); apply: eq_holds f_e' => j /=.
move/(_ j): ee'; rewrite [j]d_eq !nth_row_env nth_set_nth /=.
case: eqP => [-> | ne_j_k -> //]; first by rewrite mxE.
apply/mapP=> [[r lt_r_d]]; rewrite -d_eq => def_j; case: ne_j_k.
by rewrite def_j divn_addl_mul // divn_small ?addn0.
Qed.

End Env.

Section DecideRed.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation F G n.

Definition submodmx_form (U : 'M[term]_n) :=
  \big[And/True]_(x \in G) subsetmx_form (mulmx_term U (mx_term (rG x))) U.

Lemma submodmx_form_qf : forall U, qf_form (submodmx_form U).
Proof.
move=> U; rewrite (morphAnd (@qf_form _)) ?big1 //= => x _.
by rewrite subsetmx_form_qf.
Qed.

Lemma eval_submodmx : forall U e,
   qf_eval e (submodmx_form U) = submodmx rG (eval_mx e U).
Proof.
move=> U e; rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/submodmxP=> Umod x; move/implyP: (Umod x);
  by rewrite eval_subsetmx eval_mulmx eval_mx_term.
Qed.

Definition redmx_form :=
  let Ut := vec_mx (row_var (n * n) 0) in
  let properUt := (~ mxrank_form 0 Ut /\ ~ mxrank_form n Ut)%T in
  let redUt := (submodmx_form Ut /\ properUt)%T in
  (Bool (n > 0) ==> Exists_row_form (n * n) 0 redUt)%T.
Definition redmx_sat := GRing.sat (@row_env (n * n) [::]) redmx_form.

Lemma mx_red_satP : reflect (mx_reducible rG) redmx_sat.
Proof.
rewrite /redmx_sat {1}/redmx_form; set Ut := vec_mx _ => /=.
set redUt := (_ /\ _)%T; pose red U := submodmx rG U && (0 < \rank U < n).
have: qf_form redUt by rewrite /= submodmx_form_qf !mxrank_form_qf.
move/GRing.qf_evalP; set qev := @GRing.qf_eval _ => qevP.
have qev_red: forall u, qev (row_env [:: u]) redUt = red (vec_mx u).
  move=> u; rewrite /red lt0n ltn_neqAle rank_leq_col /qev /= !eval_mxrank.
  by rewrite eval_submodmx andbT eval_vec_mx eval_row_var.
apply: (iffP satP) => /= redG n_gt0; move/(_ n_gt0): redG.
  case/Exists_rowP; rewrite ?muln_gt0 ?n_gt0 // => u; move/qevP.
  by rewrite qev_red; exists (vec_mx u).
case=> U; rewrite -/(red U) -[U]mxvecK -qev_red; move/qevP=> redU.
by apply/Exists_rowP; rewrite ?muln_gt0 ?n_gt0 //; exists (mxvec U).
Qed.

End DecideRed.

End MatrixFormula.

End MatrixFormula.

(* Matrix parametricity for the constructions in this file. *)
Section MapVecMatrix.

Variables (aT rT : Type) (f : aT -> rT).
Notation "A ^f" := (map_mx f A) : ring_scope.

Variables (m n : nat) (A : 'M[aT]_(m, n)).

Lemma map_mxvec : (mxvec A)^f = mxvec A^f.
Proof. by apply/rowP=> i; rewrite !(castmxE, mxE). Qed.

Lemma map_vec_mx : forall v : 'rV_(m * n), (vec_mx v)^f = vec_mx v^f.
Proof. by move=> v; apply/matrixP=> i j; rewrite !mxE. Qed.

End MapVecMatrix.

Section MapLinMatrix.

Variables (aR rR : ringType) (f : aR -> rR).
Hypothesis fRM : GRing.morphism f.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma map_lin1_mx : forall m n (g : 'rV_m -> 'rV_n) gf, 
  (forall v, (g v)^f = gf v^f) -> (lin1_mx g)^f = lin1_mx gf.
Proof.
move=> m n g gf def_gf; apply/matrixP=> i j.
by rewrite !mxE -(map_delta_mx fRM) -def_gf mxE.
Qed.

Lemma map_lin_mx : forall m1 n1 m2 n2 (g : 'M_(m1, n1) -> 'M_(m2, n2)) gf, 
  (forall A, (g A)^f = gf A^f) -> (lin_mx g)^f = lin_mx gf.
Proof.
move=> m1 n1 m2 n2 g gf def_gf; apply: map_lin1_mx => A /=.
by rewrite map_mxvec def_gf map_vec_mx.
Qed.

End MapLinMatrix.

(* Change of representation field (by tensoring) *)
Section ChangeOfField.

Variables (aF rF : fieldType) (f : aF -> rF).
Hypothesis fRM : GRing.morphism f.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Section MapMatrixRepr.

Lemma map_cent_mx : forall m n (E : 'M_(m, n * n)),
  (cent_mx E)^f = cent_mx E^f.
Proof.
move=> m n E; rewrite map_kermx //; congr (kermx _); apply: map_lin_mx => // A.
rewrite map_mxM //; congr (_ *m _); apply: map_lin_mx => //= B.
by rewrite map_mx_sub ? map_mxM.
Qed.

Lemma map_mx_is_scalar : forall n (A : 'M_n), is_scalar_mx A^f = is_scalar_mx A.
Proof.
by move=> n A; rewrite /is_scalar_mx -(subsetmx_map fRM) !map_mxvec map_mx1.
Qed.

End MapMatrixRepr.

Section MapMinpoly.

Variable n' : nat.
Local Notation n := n'.+1.
Let mfRM := map_mxRM fRM n'.

Variable A : 'M[aF]_n.
Local Notation fp := (map_poly f).

Lemma map_minpoly_mx : forall e, (minpoly_mx A e)^f = minpoly_mx A^f e.
Proof.
move=> e; apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec.
by rewrite (ringM_exp (map_mxRM fRM _)).
Qed.

Lemma degree_mxminpoly_map : degree_mxminpoly A^f = degree_mxminpoly A.
Proof. by apply: eq_ex_minn => e; rewrite -map_minpoly_mx mxrank_map. Qed.

Lemma mxminpoly_map : mxminpoly A^f = fp (mxminpoly A).
Proof.
rewrite (ringM_sub (map_polyRM fRM)); congr (_ - _).
  by rewrite map_polyXn // degree_mxminpoly_map.
rewrite degree_mxminpoly_map -(ringM_exp (map_mxRM fRM _)).
apply/polyP=> i; rewrite coef_map // !coef_rVpoly degree_mxminpoly_map.
case/insub: i => [i|]; last by rewrite ringM_0.
by rewrite -map_minpoly_mx -map_pinvmx // -map_mxvec -map_mxM // mxE.
Qed.

Lemma map_horner_mx : forall p, (horner_mx A p)^f = horner_mx A^f (fp p).
Proof.
move=> p; rewrite ![horner_mx _ _]horner_poly size_map_poly // map_mx_sum //.
apply: eq_bigr => i _; rewrite coef_map // map_mxM // map_scalar_mx //.
by rewrite (ringM_exp mfRM).
Qed.

End MapMinpoly.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation aF G n.

Definition map_repr_mx of GRing.morphism f := fun g => (rG g)^f.

Lemma map_mx_repr : mx_repr G (map_repr_mx fRM).
Proof.
split=> [|x y Gx Gy]; first by rewrite /map_repr_mx repr_mx1 map_mx1.
by rewrite -map_mxM // -repr_mxM.
Qed.
Canonical Structure map_repr := MxRepresentation map_mx_repr.
Local Notation rGf := map_repr.

Lemma map_reprE : forall x, rGf x = (rG x)^f. Proof. by []. Qed.

Lemma map_reprJ : forall m (A : 'M_(m, n)) x, (A *m rG x)^f = A^f *m rGf x.
Proof. move=> m A x; exact: map_mxM. Qed.

Lemma map_enveloping_algebra_mx :
  (enveloping_algebra_mx rG)^f = enveloping_algebra_mx rGf.
Proof. by apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec. Qed.

Lemma map_rfix_mx : (rfix_mx rG)^f = rfix_mx rGf.
Proof.
rewrite map_kermx //; congr (kermx _); apply: map_lin1_mx => //= v.
rewrite map_mxvec (map_mx_sub fRM) !(map_mxM fRM) map_const_mx (ringM_1 fRM).
rewrite map_enveloping_algebra_mx; congr (mxvec (_ *m _ - _)).
by apply: map_lin1_mx => //= w; rewrite map_mxM ?map_vec_mx.
Qed.

Lemma rcent_map : forall A, rcent rGf A^f = rcent rG A.
Proof.
move=> A; apply/setP=> x; rewrite !inE -!map_mxM ?inj_eq //; exact: map_mx_inj.
Qed.

Lemma rstab_map : forall m (U : 'M_(m, n)), rstab rGf U^f = rstab rG U.
Proof.
move=> m U; apply/setP=> x; rewrite !inE -!map_mxM ?inj_eq //.
exact: map_mx_inj.
Qed.

Lemma rstabs_map : forall m (U : 'M_(m, n)), rstabs rGf U^f = rstabs rG U.
Proof. by move=> m A; apply/setP=> x; rewrite !inE -!map_mxM ?subsetmx_map. Qed.

Lemma centgmx_map : forall A, centgmx rGf A^f = centgmx rG A.
Proof. by move=> A; rewrite /centgmx rcent_map. Qed.

Lemma submodmx_map : forall U, submodmx rGf U^f = submodmx rG U.
Proof. by move=> U; rewrite /submodmx rstabs_map. Qed.

Lemma mx_irr_map : mx_irreducible rGf -> mx_irreducible rG.
Proof.
move=> irrGf redG; case: irrGf; case/redG=> U; exists U^f.
by rewrite submodmx_map mxrank_map.
Qed. 

Lemma rker_map : rker rGf = rker rG.
Proof. by rewrite /rker -rstab_map map_mx1. Qed.

Lemma map_mx_repr_faithful : mx_repr_faithful rGf = mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_map. Qed.

Lemma map_mx_abs_irr :
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG. 
Proof.
by rewrite /mx_absolutely_irreducible -map_enveloping_algebra_mx row_full_map.
Qed.

End ChangeOfField.

(* Construction of a splitting field FA of an irreducible representation, for *)
(* a matrix A in the centraliser of the representation. FA is the row-vector  *)
(* space of the matrix algebra generated by A with basis 1, A, ..., A ^+ d.-1 *)
(* or, equivalently, the polynomials in {poly F} taken mod the (irreducible)  *)
(* minimal polynomial pA of A (of degree d).                                  *)
(* The details of the construction of FA are encapsulated in a submodule.     *)
Module MatrixGenField.

Section GenField.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).

Local Notation d := (degree_mxminpoly A).
Local Notation Ad := (minpoly_mx A d).
Local Notation pA := (mxminpoly A).
Let d_gt0 := mxminpoly_nonconstant A.
Local Notation irr := mx_irreducible.

Record gen_of (irrG : irr rG) (cGA : centgmx rG A) := Gen {rVval : 'rV[F]_d}.
Prenex Implicits rVval.

Hypotheses (irrG : irr rG) (cGA : centgmx rG A).

Notation FA := (gen_of irrG cGA).
Let inFA := Gen irrG cGA.

Canonical Structure gen_subType :=
  Eval hnf in [newType for rVval by @gen_of_rect irrG cGA].
Definition gen_eqMixin := Eval hnf in [eqMixin of FA by <:].
Canonical Structure gen_eqType := Eval hnf in EqType FA gen_eqMixin.
Definition  gen_choiceMixin := [choiceMixin of FA by <:].
Canonical Structure  gen_choiceType :=
  Eval hnf in ChoiceType FA gen_choiceMixin.

Definition gen0 := inFA 0.
Definition genN (x : FA) := inFA (- val x).
Definition genD (x y : FA) := inFA (val x + val y).

Lemma gen_addA : associative genD.
Proof. by move=> x y z; apply: val_inj; rewrite /= addrA. Qed.

Lemma gen_addC : commutative genD.
Proof. by move=> x y; apply: val_inj; rewrite /= addrC. Qed.

Lemma gen_add0r : left_id gen0 genD.
Proof. by move=> x; apply: val_inj; rewrite /= add0r. Qed.

Lemma gen_addNr : left_inverse gen0 genN genD.
Proof. by move=> x; apply: val_inj; rewrite /= addNr. Qed.

Definition gen_zmodMixin := ZmodMixin gen_addA gen_addC gen_add0r gen_addNr.
Canonical Structure  gen_zmodType := Eval hnf in ZmodType FA gen_zmodMixin.

Definition pval (x : FA) := rVpoly (val x).

Definition mxval (x : FA) := horner_mx A (pval x).

Definition gen (x : F) := inFA (poly_rV x%:P).

Lemma genK : forall x, mxval (gen x) = x%:M.
Proof.
move=> x; rewrite /mxval [pval _]poly_rV_K ?horner_mx_C // size_polyC.
by case: (x != 0).
Qed.
Let zRM := @scalar_mxRM F n'.

Lemma mxval_inj : injective mxval.
Proof. exact: inj_comp (@horner_rVpoly_inj _ _ A) val_inj. Qed.

Let mxRM := horner_mxRM A.

Lemma mxval0 : mxval 0 = 0.
Proof. by rewrite /mxval [pval _]rVpoly0 (ringM_0 mxRM). Qed.

Lemma mxvalN : {morph mxval : x / - x}.
Proof. by move=> x; rewrite /mxval [pval _]rVpolyN (ringM_opp mxRM). Qed.

Lemma mxvalD : {morph mxval : x y / x + y}.
Proof. by move=> x y; rewrite /mxval [pval _]rVpolyD (ringM_add mxRM). Qed.

Definition mxval_sum := big_morph mxval mxvalD mxval0.

Definition gen1 := inFA (poly_rV 1).
Definition genM x y := inFA (poly_rV (pval x * pval y %% pA)).
Definition genV x := inFA (poly_rV (mx_inv_horner A (mxval x)^-1)).

Lemma mxval_gen1 : mxval gen1 = 1%:M.
Proof. by rewrite /mxval [pval _]poly_rV_K ?size_poly1 // horner_mx_C. Qed.

Lemma mxval_genM : {morph mxval : x y / genM x y >-> x *m y}.
Proof.
move=> x y; rewrite /mxval [pval _]poly_rV_K ?size_mod_mxminpoly //.
by rewrite -horner_mxK mx_inv_hornerK ?horner_mx_sub // (ringM_mul mxRM).
Qed.

Lemma mxval_genV : {morph mxval : x / genV x >-> invmx x}.
Proof.
move=> x; rewrite /mxval [pval _]poly_rV_K ?size_poly ?mx_inv_hornerK //.
pose m B : 'M[F]_(n * n) := lin_mx (mulmxr B); set B := mxval x.
case uB: (GRing.unit B); last by rewrite invr_out ?uB ?horner_mx_sub.
have defAd: Ad = Ad *m m B *m m B^-1.
  apply/row_matrixP=> i.
  by rewrite !row_mul mul_rV_lin /= mx_rV_lin /= mulmxK ?vec_mxK.
rewrite -[B^-1]mul1mx -(mul_vec_lin (mulmxr_linear _ _)) defAd subsetmxMr //.
rewrite -mxval_gen1 (subsetmx_trans (horner_mx_sub _ _)) // {1}defAd.
rewrite -(geq_leqif (mxrank_leqif_sup _)) ?mxrankM_maxl // -{}defAd.
apply/row_subP=> i; rewrite row_mul rowK mul_vec_lin /= -horner_mx_Xn.
by rewrite -[_ *m _](ringM_mul mxRM) horner_mx_sub.
Qed.

Lemma gen_mulA : associative genM.
Proof. by move=> x y z; apply: mxval_inj; rewrite !mxval_genM mulmxA. Qed.

Lemma gen_mulC : commutative genM.
Proof. by move=> x y; rewrite /genM mulrC. Qed.

Lemma gen_mul1r : left_id gen1 genM.
Proof. by move=> x; apply: mxval_inj; rewrite mxval_genM mxval_gen1 mul1mx. Qed.

Lemma gen_mulDr : left_distributive genM +%R.
Proof.
by move=> x y z; apply: mxval_inj; rewrite !(mxvalD, mxval_genM) mulmx_addl.
Qed.

Lemma gen_ntriv : gen1 != 0.
Proof. by rewrite -(inj_eq mxval_inj) mxval_gen1 mxval0 oner_eq0. Qed.

Definition gen_ringMixin :=
  ComRingMixin gen_mulA gen_mulC gen_mul1r gen_mulDr gen_ntriv.

Canonical Structure gen_ringType := Eval hnf in RingType FA gen_ringMixin.
Canonical Structure gen_comRingType := Eval hnf in ComRingType FA gen_mulC.

Lemma mxval1 : mxval 1 = 1%:M. Proof. exact: mxval_gen1. Qed.

Lemma mxvalM : {morph mxval : x y / x * y >-> x *m y}.
Proof. exact: mxval_genM. Qed.

Lemma mxvalRM : GRing.morphism mxval.
Proof. by split=> [x y|x y|]; rewrite ?mxvalM ?mxval1 // mxvalD mxvalN. Qed.
Hint Resolve mxvalRM.

Lemma mxval_centg : forall x, centgmx rG (mxval x).
Proof.
move=> x; rewrite [mxval _]horner_rVpoly -subsetmx_cent_envelop vec_mxK.
rewrite {x}subsetmxMtrans //; apply/row_subP=> k.
rewrite rowK subsetmx_cent_envelop; apply/centgmxP => g Gg /=.
by rewrite !mulmxE commr_exp // /GRing.comm -mulmxE (centgmxP _ _ cGA).
Qed.

Lemma gen_mulVr : GRing.Field.axiom genV.
Proof.
move=> x; rewrite -(inj_eq mxval_inj) mxval0; move/eqP => nz_x.
case: (mx_Schur irrG (mxval_centg x)) => {nz_x}// u_x.
by apply: mxval_inj; rewrite mxvalM mxval_genV mxval1 mulVmx.
Qed.

Lemma gen_invr0 : genV 0 = 0.
Proof. by apply: mxval_inj; rewrite mxval_genV !mxval0 -{2}invr0. Qed.

Definition gen_unitRingMixin := FieldUnitMixin gen_mulVr gen_invr0.
Canonical Structure gen_unitRingType :=
  Eval hnf in UnitRingType FA gen_unitRingMixin.
Canonical Structure gen_comUnitRingType :=
  Eval hnf in [comUnitRingType of FA].
Definition gen_fieldMixin :=
  @FieldMixin _ _ _ _ : GRing.Field.mixin_of gen_unitRingType.
Definition gen_idomainMixin := FieldIdomainMixin gen_fieldMixin.
Canonical Structure gen_idomainType :=
  Eval hnf in IdomainType FA gen_idomainMixin.
Canonical Structure gen_fieldType :=
  Eval hnf in FieldType FA gen_fieldMixin.

Lemma mxvalV : {morph mxval : x / x^-1 >-> invmx x}.
Proof. exact: mxval_genV. Qed.

Lemma genRM : GRing.morphism gen.
Proof.
split=> // [x y | x y]; apply: mxval_inj.
  by rewrite mxvalD mxvalN !genK (ringM_sub zRM).
by rewrite mxvalM !genK (ringM_mul zRM).
Qed.
Hint Resolve genRM.

(* The generated field contains a root of the minimal polynomial (in some  *)
(* cases we want to use the construction solely for that purpose).         *)

Definition groot := inFA (poly_rV ('X %% pA)).

Lemma mxval_groot : mxval groot = A.
Proof.
rewrite /mxval [pval _]poly_rV_K ?size_mod_mxminpoly // -horner_mxK.
by rewrite mx_inv_hornerK ?horner_mx_sub // horner_mx_X.
Qed.

Lemma mxval_grootX : forall k, mxval (groot ^+ k) = A ^+ k.
Proof. by move=> k; rewrite ringM_exp // mxval_groot. Qed.

Lemma map_mxminpoly_groot : (map_poly gen pA).[groot] = 0.
Proof.
apply: mxval_inj; rewrite -(horner_map mxvalRM) mxval_groot.
rewrite mxval0 -(mx_root_minpoly A); congr ((_ : {poly _}).[A]).
by apply/polyP=> i; rewrite 3?coef_map ?genK.
Qed.

(* Plugging the extension morphism gen into the ext_repr construction   *)
(* yields a (reducible) tensored representation.                           *)

Lemma non_linear_gen_reducible : d > 1 -> mx_reducible (map_repr genRM rG).
Proof.
rewrite ltnNge mxminpoly_linear_is_scalar => Anscal _.
pose Af := map_mx gen A; exists (kermx (Af - groot%:M)).
apply/and3P; split; last 1 first.
- rewrite mxrank_ker -subn_gt0 subKn ?rank_leq_row // lt0n mxrank_eq0 subr_eq0.
  apply: contra Anscal => Af_scal; rewrite -(map_mx_is_scalar genRM) -/Af.
  by apply/is_scalar_mxP; exists groot; apply/eqP.
- apply/submodmxP=> g Gg; apply/subsetmx_kerP; rewrite -mulmxA.
  rewrite -(centgmxP (map_repr genRM rG) (Af - _) _) //.
    by rewrite mulmxA [kermx _ *m _]mulmx_ker mul0mx.
  apply/centgmxP=> z Gz; rewrite mulmx_subl mulmx_subr scalar_mxC.
  by rewrite -!map_mxM 1?(centgmxP _ _ cGA).
rewrite lt0n mxrank_ker subn_eq0 row_leq_rank; apply/row_freeP=> [[XA' XAK]].
have pAf0: (mxminpoly Af).[groot] == 0.
  by rewrite mxminpoly_map ?map_mxminpoly_groot.
have{pAf0} [q def_pAf]:= factor_theorem _ _ pAf0.
have q_nz: q != 0.
  case: eqP (congr1 (fun p : {poly _} => size p) def_pAf) => // ->.
  by rewrite size_mxminpoly mul0r size_poly0.
have qAf0: horner_mx Af q = 0.
  rewrite -[_ q]mulr1 -[1]XAK mulrA -{2}(horner_mx_X Af) -(horner_mx_C Af).
  rewrite -(ringM_sub (horner_mxRM Af)) -(ringM_mul (horner_mxRM Af)) -def_pAf.
  by rewrite mx_root_minpoly mul0r.
have{qAf0} := size_dvdp q_nz (mxminpoly_min qAf0); rewrite def_pAf.
by rewrite size_mul_monic ?monic_factor // seq_factor addn2 ltnn.
Qed.

(* An alternative to the above, used in the proof of the p-stability of       *)
(* groups of odd order, is to reconsider the original vector space as a       *)
(* vector space of dimension n / e over FA. This is applicable only if G is   *)
(* the largest group represented on the original vector space (i.e., if we    *)
(* are not studying a representation of G induced by one of a larger group,   *)
(* as in B & G Theorem 2.6 for instance). We can't fully exploit one of the   *)
(* benefits of this approach -- that the type domain for the vector space can *)
(* remain unchanged -- because we're restricting ourselves to row matrices;   *)
(* we have to use explicit bijections to convert between the two views.       *)

Definition subbase m (B : 'rV_m) : 'M_(m * d, n) :=
  \matrix_ik mxvec (\matrix_(i, k) (row (B 0 i) (A ^+ k))) 0 ik.

Lemma gen_dim_proof : exists m', existsb B : 'rV_(n - m'), row_free (subbase B).
Proof. by exists n%N; apply/existsP; exists 0; rewrite subnn. Qed.

Definition gen_dim := (n - ex_minn gen_dim_proof)%N.
Notation m := gen_dim.

Definition gen_base : 'rV_m :=
  if (pick [pred B | row_free (subbase B)]) is Some B then B else 0.
Definition base := subbase gen_base.

Lemma base_free : row_free base.
Proof.
rewrite /base /gen_base /m; case: pickP => //; case: ex_minnP => m_max.
by case/existsP=> B Bfree _; move/(_ B); case/idP.
Qed.

Lemma base_full : row_full base.
Proof.
rewrite /row_full (eqnP base_free) /m; case: ex_minnP => m'.
set m := (n - m')%N; case/existsP=> /= B; move/eqnP=> Bfree m_min.
rewrite -Bfree eqn_leq rank_leq_col; case: (posnP m') => [m'0 | m'_gt0] /=.
  by rewrite Bfree /m m'0 subn0 leq_pmulr.
rewrite -{1}(mxrank1 F n) mxrankS //; apply/row_subP=> j.
move/implyP: {m_min}(m_min m'.-1); rewrite -ltnS prednK // ltnn implybF.
apply: contraR => nBj; apply/existsP; rewrite -subSS prednK //.
case: (posnP (n.+1 - m')) => [-> |]; first by exists 0.
rewrite subn_gt0 ltnS; move/leq_subS->; rewrite -(add1n m).
exists (row_mx (const_mx j) B); rewrite -row_leq_rank.
pose Bj := Ad *m lin1_mx (mulmx (row j 1%:M) \o vec_mx).
have rBj: \rank Bj = d.
  apply/eqP; rewrite eqn_leq rank_leq_row -subn_eq0 -mxrank_ker mxrank_eq0.
  apply/rowV0P=> u; move/subsetmx_kerP; rewrite mulmxA mul_rV_lin1 /=.
  rewrite -horner_rVpoly; pose x := inFA u; rewrite -/(mxval x).
  case: (eqVneq x 0) => [[] // | nzx].
  move/(congr1 (mulmx^~ (mxval x^-1))); rewrite mul0mx /= -mulmxA -mxvalM.
  rewrite divff // mxval1 mulmx1.
  by move/rowP; move/(_ j); move/eqP; rewrite !mxE !eqxx oner_eq0.
rewrite {1}mulSn -Bfree -{1}rBj {rBj} -mxrank_direct_sum.
  rewrite mxrankS // gsummx_sub; apply/andP; split.
    apply/row_subP=> k; rewrite row_mul mul_rV_lin1 /=.
    apply: eq_row_sub (mxvec_index (lshift _ 0) k) _.
    by rewrite !rowK mxvecK mxvecE mxE row_mxEl mxE -row_mul mul1mx.
  apply/row_subP=> ik; case/mxvec_indexP: ik => i k.
  apply: eq_row_sub (mxvec_index (rshift 1 i) k) _.
  by rewrite !rowK !mxvecE 2!mxE row_mxEr.
apply/eqP; apply/rowV0P=> v; rewrite sub_capmx; case/andP; case/subsetmxP=> u.
set x := inFA u; rewrite {Bj}mulmxA mul_rV_lin1 /= -horner_rVpoly -/(mxval x).
move: (eqVneq x 0) => [-> | nzx ->]; first by rewrite mxval0 mulmx0.
move/(subsetmxMr (mxval x^-1)); rewrite -mulmxA -mxvalM divff {nzx}//.
rewrite mxval1 mulmx1 => Bx'j.
rewrite (subsetmx_trans Bx'j) in nBj => {nBj Bx'j} //; apply/row_subP.
case/mxvec_indexP=> i k; rewrite row_mul rowK mxvecE mxE rowE -mulmxA.
have ->: A ^+ k *m mxval x^-1 = mxval (groot ^+ k / x).
  by rewrite mxvalM (ringM_exp mxvalRM) mxval_groot.
rewrite [mxval _]horner_rVpoly; move: {k u x}(val _) => u.
rewrite (mulmx_sum_row u) !linear_sum subsetmx_sum //= => k _.
rewrite !linearZ subsetmx_scale //= rowK mxvecK -rowE.
by apply: eq_row_sub (mxvec_index i k) _; rewrite rowK mxvecE mxE.
Qed.

Lemma gen_dim_factor : (m * d)%N = n.
Proof. by rewrite -(eqnP base_free) (eqnP base_full). Qed.

Lemma gen_dim_gt0 : m > 0.
Proof. by case: posnP gen_dim_factor => // ->. Qed.

Section Bijection.

Variable m1 : nat.

Definition in_gen (W : 'M[F]_(m1, n)) : 'M[FA]_(m1, m) :=
  \matrix_(i, j) inFA (row j (vec_mx (row i W *m pinvmx base))).

Definition val_gen (W : 'M[FA]_(m1, m)) : 'M[F]_(m1, n) :=
  \matrix_i (mxvec (\matrix_j val (W i j)) *m base).

Lemma in_genK : cancel in_gen val_gen.
Proof.
move=> W; apply/row_matrixP=> i; rewrite rowK; set w := row i W.
have b_w: (w <= base)%MR by rewrite subsetmx_full ?base_full.
rewrite -{b_w}(mulmxKpV b_w); congr (_ *m _).
by apply/rowP; case/mxvec_indexP=> j k; rewrite mxvecE !mxE.
Qed.

Lemma val_genK : cancel val_gen in_gen.
Proof.
move=> W; apply/matrixP=> i j; apply: val_inj; rewrite mxE /= rowK.
case/row_freeP: base_free => B' BB'; rewrite -[_ *m _]mulmx1 -BB' mulmxA.
by rewrite mulmxKpV ?subsetmxMl // -mulmxA BB' mulmx1 mxvecK rowK.
Qed.

Lemma in_gen0 : in_gen 0 = 0.
Proof. by apply/matrixP=> i j; rewrite !mxE !(mul0mx, linear0). Qed.

Lemma val_gen0 : val_gen 0 = 0.
Proof. by apply: (canLR in_genK); rewrite in_gen0. Qed.

Lemma in_genN : {morph in_gen : W / - W}.
Proof.
move=> W; apply/matrixP=> i j; apply: val_inj.
by rewrite !mxE !(mulNmx, linearN).
Qed.

Lemma val_genN : {morph val_gen : W / - W}.
Proof. by move=> W; apply: (canLR in_genK); rewrite in_genN val_genK. Qed.

Lemma in_genD : {morph in_gen : U V / U + V}.
Proof.
move=> U V; apply/matrixP=> i j; apply: val_inj.
by rewrite !mxE !(mulmx_addl, linearD).
Qed.

Lemma val_genD : {morph val_gen : U V / U + V}.
Proof. by move=> U V; apply: (canLR in_genK); rewrite in_genD !val_genK. Qed.

Definition in_gen_sum := big_morph in_gen in_genD in_gen0.
Definition val_gen_sum := big_morph val_gen val_genD val_gen0.

Lemma in_genZ : forall a, {morph in_gen : W / a *m: W >-> gen a *m: W}.
Proof.
move=> a W; apply/matrixP=> i j; apply: mxval_inj.
rewrite !mxE mxvalM genK ![mxval _]horner_rVpoly /=.
by rewrite mul_scalar_mx !(I, scalemxAl, linearZ).
Qed.

End Bijection.

Prenex Implicits val_genK in_genK.

Lemma val_gen_rV : forall w : 'rV_m,
  val_gen w = mxvec (\matrix_j val (w 0 j)) *m base.
Proof. by move=> w; apply/rowP=> j; rewrite mxE. Qed.

Section Bijection2.

Variable m1 : nat.

Lemma val_gen_row : forall W (i : 'I_m1), val_gen (row i W) = row i (val_gen W).
Proof.
move=> W i; rewrite val_gen_rV rowK; congr (mxvec _ *m _).
by apply/matrixP=> j k; rewrite !mxE.
Qed.

Lemma in_gen_row : forall W (i : 'I_m1), in_gen (row i W) = row i (in_gen W).
Proof. by move=> W i; apply: (canLR val_genK); rewrite val_gen_row in_genK. Qed.

Lemma row_gen_sum_mxval : forall W (i : 'I_m1),
  row i (val_gen W) = \sum_j row (gen_base 0 j) (mxval (W i j)).
Proof.
move=> W i; rewrite -val_gen_row [row i W]row_sum_delta val_gen_sum.
apply: eq_bigr => /= j _; rewrite mxE; move: {W i}(W i j) => x.
have ->: x = \sum_k gen (val x 0 k) * inFA (delta_mx 0 k).
  case: x => u; apply: mxval_inj; rewrite {1}[u]row_sum_delta.
  rewrite mxval_sum [mxval _]horner_rVpoly mulmx_suml linear_sum /=.
  apply: eq_bigr => k _; rewrite mxvalM genK [mxval _]horner_rVpoly /=.
  by rewrite mul_scalar_mx -scalemxAl linearZ.
rewrite scalemx_suml val_gen_sum mxval_sum linear_sum; apply: eq_bigr => k _.
rewrite mxvalM genK mul_scalar_mx linearZ [mxval _]horner_rVpoly /=.
rewrite -scalemxA; apply: (canLR in_genK); rewrite in_genZ; congr (_ *m: _).
apply: (canRL val_genK); transitivity (row (mxvec_index j k) base); last first.
  by rewrite -rowE rowK mxvecE mxE rowK mxvecK.
rewrite rowE -mxvec_delta -[val_gen _](row_id 0) rowK /=; congr (mxvec _ *m _).
apply/row_matrixP=> j'; rewrite rowK !mxE mulr_natr rowE mul_delta_mx_cond.
by rewrite !mulrb (fun_if rVval).
Qed.

Lemma val_genZ : forall x, {morph @val_gen m1 : W / x *m: W >-> W *m mxval x}.
Proof.
move=> x W; apply/row_matrixP=> i; rewrite row_mul !row_gen_sum_mxval.
by rewrite mulmx_suml; apply: eq_bigr => j _; rewrite mxE mulrC mxvalM row_mul.
Qed.

End Bijection2.

Lemma subsetmx_in_gen : forall m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)),
  (U <= V -> in_gen U <= in_gen V)%MR.
Proof.
move=> m1 m2 U V sUV; apply/row_subP=> i; rewrite -in_gen_row.
case/subsetmxP: (row_subP _ _ sUV i) => u ->{i}.
rewrite mulmx_sum_row in_gen_sum subsetmx_sum // => j _.
by rewrite in_genZ in_gen_row subsetmx_scale ?row_sub.
Qed.

Lemma subsetmx_in_gen_eq : forall m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)),
  (V *m A <= V -> (in_gen U <= in_gen V) = (U <= V))%MR.
Proof.
move=> m1 m2 U V sVA_V; apply/idP/idP=> siUV; last exact: subsetmx_in_gen.
apply/row_subP=> i; rewrite -[row i U]in_genK in_gen_row.
case/subsetmxP: (row_subP _ _ siUV i) => u ->{i U siUV}.
rewrite mulmx_sum_row val_gen_sum subsetmx_sum // => j _.
rewrite val_genZ val_gen_row in_genK rowE -mulmxA subsetmxMtrans //.
rewrite [mxval _]horner_poly mulmx_sumr subsetmx_sum // => [[k _]] _ /=.
rewrite mulmxA mul_mx_scalar -scalemxAl subsetmx_scale {u j}//.
elim: k => [|k IHk]; first by rewrite mulmx1.
by rewrite exprSr mulmxA (subsetmx_trans (subsetmxMr A IHk)).
Qed.

Definition gen_mx g := \matrix_i in_gen (row (gen_base 0 i) (rG g)).

Let val_genJmx : forall m,
  {in G, forall g, {morph @val_gen m : W / W *m gen_mx g >-> W *m rG g}}.
Proof.
move=> m g Gg /= W; apply/row_matrixP=> i; rewrite -val_gen_row !row_mul.
rewrite mulmx_sum_row val_gen_sum row_gen_sum_mxval mulmx_suml.
apply: eq_bigr => /= j _; rewrite val_genZ rowK in_genK mxE -!row_mul.
by rewrite (centgmxP _ _ (mxval_centg _)).
Qed.

Lemma gen_mx_repr : mx_repr G gen_mx.
Proof.
split=> [|g h Gg Gh]; apply: (can_inj val_genK).
  by rewrite -[gen_mx 1]mul1mx val_genJmx // repr_mx1 mulmx1.
rewrite {1}[val_gen]lock -[gen_mx g]mul1mx !val_genJmx // -mulmxA -repr_mxM //.
by rewrite -val_genJmx ?groupM ?mul1mx -?lock.
Qed.
Canonical Structure gen_repr := MxRepresentation gen_mx_repr.
Local Notation rGA := gen_repr.

Lemma val_genJ : forall m,
  {in G, forall g, {morph @val_gen m : W / W *m rGA g >-> W *m rG g}}.
Proof. exact: val_genJmx. Qed.

Lemma in_genJ : forall m,
  {in G, forall g, {morph @in_gen m : v / v *m rG g >-> v *m rGA g}}.
Proof.
by move=> m g Gg /= v; apply: (canLR val_genK); rewrite val_genJ ?in_genK.
Qed.

Lemma gen_rfix_mx : (rfix_mx rGA :=: in_gen (rfix_mx rG))%MR.
Proof.
apply/eqmxP; apply/andP; split; last first.
  by apply/subsetmx_rfixP=> g Gg; rewrite -in_genJ ?(subsetmx_rfixP rG _ _).
rewrite -[rfix_mx rGA]val_genK; apply: subsetmx_in_gen.
by apply/subsetmx_rfixP=> g Gg; rewrite -val_genJ ?(subsetmx_rfixP rGA _ _).
Qed.

Definition rowval_gen m1 U :=
  <<\matrix_ik
      mxvec (\matrix_(i < m1, k < d) (row i (val_gen U) *m A ^+ k)) 0 ik>>%MR.

Lemma subsetmx_rowval_gen : forall m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, m)),
  (U <= rowval_gen V)%MR = (in_gen U <= V)%MR.
Proof.
move=> m1 m2 U V; rewrite eqmx_gen; apply/idP/idP=> sUV.
  apply: subsetmx_trans (subsetmx_in_gen sUV) _.
  apply/row_subP; case/mxvec_indexP=> i k; rewrite -in_gen_row rowK mxvecE mxE.
  rewrite -mxval_grootX -val_gen_row -val_genZ val_genK subsetmx_scale //.
  exact: row_sub.
rewrite -[U]in_genK; case/subsetmxP: sUV => u ->{U}.
apply/row_subP=> i0; rewrite -val_gen_row row_mul; move: {i0 u}(row _ u) => u.
rewrite mulmx_sum_row val_gen_sum subsetmx_sum // => i _.
rewrite val_genZ [mxval _]horner_rVpoly [_ *m Ad]mulmx_sum_row.
rewrite !linear_sum subsetmx_sum // => k _.
rewrite !linearZ subsetmx_scale {u}//= rowK mxvecK val_gen_row.
by apply: (eq_row_sub (mxvec_index i k)); rewrite rowK mxvecE mxE.
Qed.

Lemma rowval_genK : forall m1 (U : 'M_(m1, m)),
  (in_gen (rowval_gen U) :=: U)%MR.
Proof.
move=> m1 U; apply/eqmxP; rewrite -subsetmx_rowval_gen subsetmx_refl /=.
by rewrite -{1}[U]val_genK subsetmx_in_gen // subsetmx_rowval_gen val_genK.
Qed.

Lemma rowval_gen_stable : forall m1 (U : 'M_(m1, m)),
  (rowval_gen U *m A <= rowval_gen U)%MR.
Proof.
move=> m1 U; rewrite -[A]mxval_groot -{1}[_ U]in_genK -val_genZ.
by rewrite subsetmx_rowval_gen val_genK subsetmx_scale // rowval_genK.
Qed.

Lemma rstab_in_gen : forall m1 (U : 'M_(m1, n)),
  rstab rGA (in_gen U) = rstab rG U.
Proof.
move=> m1 U; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
by rewrite -in_genJ // (inj_eq (can_inj in_genK)).
Qed.

Lemma rstabs_in_gen : forall m1 (U : 'M_(m1, n)),
  rstabs rG U \subset rstabs rGA (in_gen U).
Proof.
move=> m1 U; apply/subsetP=> x; rewrite !inE; case/andP=> Gx nUx.
by rewrite -in_genJ Gx // subsetmx_in_gen.
Qed.

Lemma rstabs_rowval_gen : forall m1 (U : 'M_(m1, m)),
  rstabs rG (rowval_gen U) = rstabs rGA U.
Proof.
move=> m1 U; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
by rewrite subsetmx_rowval_gen in_genJ // (eqmxMr _ (rowval_genK U)).
Qed.

Lemma submodmx_rowval_gen : forall U,
  submodmx rG (rowval_gen U) = submodmx rGA U.
Proof. by move=> U; rewrite /submodmx rstabs_rowval_gen. Qed.

Lemma gen_mx_irr : mx_irreducible rGA.
Proof.
case/(_ gen_dim_gt0)=> U; case/and3P=> Umod Unz Uproper.
case: irrG => _; exists (rowval_gen U); rewrite submodmx_rowval_gen Umod.
rewrite lt0n mxrank_eq0 -(inj_eq (can_inj in_genK)) in_gen0 -mxrank_eq0.
rewrite rowval_genK -lt0n Unz /=; apply: contraLR Uproper.
rewrite -!leqNgt !col_leq_rank => Ufull.
by rewrite -subset1mx -rowval_genK -subsetmx_rowval_gen subsetmx_full.
Qed.

Lemma rker_gen : rker rGA = rker rG.
Proof.
apply/setP=> g; rewrite !inE !mul1mx; case Gg: (g \in G) => //=.
apply/eqP/eqP=> g1.
  apply/row_matrixP=> i; apply: (can_inj in_genK).
  by rewrite rowE in_genJ //= g1 mulmx1 row1.
apply/row_matrixP=> i; apply: (can_inj val_genK).
by rewrite rowE val_genJ //= g1 mulmx1 row1.
Qed.

Lemma gen_mx_faithful : mx_repr_faithful rGA = mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_gen. Qed.

End GenField.

Section DecideGenField.

Import MatrixFormula.

Variable F : decFieldType.

Local Notation False := GRing.False.
Local Notation True := GRing.True.
Local Notation Bool b := (GRing.Bool b%bool).
Local Notation term := (GRing.term F).
Local Notation form := (GRing.formula F).

Local Notation morphAnd := (@big_morph _ _ _ true _ andb).

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Local Notation FA := (gen_of irrG cGA).
Local Notation inFA := (Gen irrG cGA).

Local Notation d := (degree_mxminpoly A).
Let d_gt0 : d > 0 := mxminpoly_nonconstant A.
Local Notation Ad := (minpoly_mx A d).

Let mxT (u : 'rV_d) := vec_mx (mulmx_term u (mx_term Ad)).

Let eval_mxT : forall e u, eval_mx e (mxT u) = mxval (inFA (eval_mx e u)).
Proof.
move=> e u; rewrite eval_vec_mx eval_mulmx eval_mx_term.
by rewrite [mxval _]horner_rVpoly.
Qed.

Let Ad'T := mx_term (pinvmx Ad).
Let mulT (u v : 'rV_d) := mulmx_term (mxvec (mulmx_term (mxT u) (mxT v))) Ad'T.

Lemma eval_mulT : forall e u v,
  eval_mx e (mulT u v) = val (inFA (eval_mx e u) * inFA (eval_mx e v)).
Proof.
move=> e u v; rewrite !(eval_mulmx, eval_mxvec) !eval_mxT eval_mx_term.
by apply: (can_inj (@rVpolyK _ _)); rewrite -mxvalM [rVpoly _]horner_rVpolyK.
Qed.

Fixpoint gen_term t := match t with
| 'X_k => row_var _ d k
| x%:T => mx_term (val (x : FA))
| n1%:R => mx_term (val (n1%:R : FA))%R
| t1 + t2 => \row_i (gen_term t1 0%R i + gen_term t2 0%R i)
| - t1 => \row_i (- gen_term t1 0%R i)
| t1 *+ n1 => mulmx_term (mx_term n1%:R%:M)%R (gen_term t1)
| t1 * t2 => mulT (gen_term t1) (gen_term t2)
| t1^-1 => gen_term t1
| t1 ^+ n1 => iter n1 (mulT (gen_term t1)) (mx_term (val (1%R : FA)))
end%T.

Definition gen_env (e : seq FA) := row_env (map val e).

Lemma nth_map_rVval : forall (e : seq FA) j, (map val e)`_j = val e`_j.
Proof.
move=> e j; case: (ltnP j (size e)) => [| leej]; first exact: (nth_map 0 0).
by rewrite !nth_default ?size_map.
Qed.

Lemma set_nth_map_rVval : forall (e : seq FA) j v,
  set_nth 0 (map val e) j v = map val (set_nth 0 e j (inFA v)).
Proof.
move=> e j v; apply: (@eq_from_nth _ 0) => [|k _].
  by rewrite !(size_set_nth, size_map).
by rewrite !(nth_map_rVval, nth_set_nth) /= nth_map_rVval [rVval _]fun_if.
Qed.

Lemma eval_gen_term : forall e t, 
  GRing.rterm t -> eval_mx (gen_env e) (gen_term t) = val (GRing.eval e t).
Proof.
move=> e; elim=> //=.
- by move=> k _; apply/rowP=> i; rewrite !mxE /= nth_row_env nth_map_rVval.
- by move=> x _; rewrite eval_mx_term.
- by move=> x _; rewrite eval_mx_term.
- move=> t1 IH1 t2 IH2; case/andP=> rt1 rt2; rewrite -{}IH1 // -{}IH2 //.
  by apply/rowP=> k; rewrite !mxE.
- by move=> t1 IH1 rt1; rewrite -{}IH1 //; apply/rowP=> k; rewrite !mxE.
- move=> t1 IH1 n1 rt1; rewrite eval_mulmx eval_mx_term mul_scalar_mx.
  by rewrite scalemx_nat {}IH1 //; elim: n1 => //= n1 IHn1; rewrite !mulrS IHn1.
- by move=> t1 IH1 t2 IH2; case/andP=> rt1 rt2; rewrite eval_mulT IH1 ?IH2.
move=> t1 IH1 n1; move/IH1=> {IH1} IH1.
elim: n1 => [|n1 IHn1] /=; first by rewrite eval_mx_term.
by rewrite eval_mulT exprS IH1 IHn1.
Qed.

(* WARNING: Coq will core dump if the Notation Bool is used in the match *)
(* pattern here.                                                         *)
Fixpoint gen_form f := match f with
| GRing.Bool b => Bool b
| t1 == t2 => mxrank_form 0 (gen_term (t1 - t2))
| GRing.Unit t1 => mxrank_form 1 (gen_term t1)
| f1 /\ f2 => gen_form f1 /\ gen_form f2
| f1 \/ f2 =>  gen_form f1 \/ gen_form f2
| f1 ==> f2 => gen_form f1 ==> gen_form f2
| ~ f1 => ~ gen_form f1
| ('exists 'X_k, f1) => Exists_row_form d k (gen_form f1)
| ('forall 'X_k, f1) => ~ Exists_row_form d k (~ (gen_form f1))
end%T.

Lemma sat_gen_form : forall e f, GRing.rformula f ->
  reflect (GRing.holds e f) (GRing.sat (gen_env e) (gen_form f)).
Proof.
have ExP := Exists_rowP; have set_val := set_nth_map_rVval.
move=> e f; elim: f e => //.
- by move=> b e _; exact: (iffP satP).
- rewrite /gen_form => t1 t2 e rt_t; set t := (_ - _)%T.
  have:= GRing.qf_evalP (gen_env e) (mxrank_form_qf 0 (gen_term t)).
  rewrite eval_mxrank mxrank_eq0 eval_gen_term // => tP.
  by rewrite (sameP satP tP) /= subr_eq0 val_eqE; exact: eqP.
- move=> f1 IH1 f2 IH2 s /=; case/andP; move/(IH1 s)=> f1P; move/(IH2 s)=> f2P.
  apply: (iffP satP) => /= [] [].
    by move/satP; move/f1P=> ?; move/satP; move/f2P=> ?.
  by move/f1P; move/satP=> ?; move/f2P; move/satP=> ?.
- move=> f1 IH1 f2 IH2 s /=; case/andP; move/(IH1 s)=> f1P; move/(IH2 s)=> f2P.
  by apply: (iffP satP) => /= [] [];
    try move/satP; do [move/f1P | move/f2P]; try move/satP; auto.
- move=> f1 IH1 f2 IH2 s /=; case/andP; move/(IH1 s)=> f1P; move/(IH2 s)=> f2P.
  by apply: (iffP satP) => /= implP;
    try move/satP; move/f1P; try move/satP; move/implP;
    try move/satP; move/f2P; try move/satP.
- move=> f1 IH1 s /=; move/(IH1 s)=> f1P.
  by apply: (iffP satP) => /= notP; try move/satP; move/f1P; try move/satP.
- move=> k f1 IHf1 s; move/IHf1=> f1P; apply: (iffP satP) => /= [|[[v f1v]]].
    by case/ExP=> // x; move/satP; rewrite set_val; move/f1P; exists (inFA x).
  by apply/ExP=> //; exists v; rewrite set_val; apply/satP; apply/f1P.
move=> i f1 IHf1 s; move/IHf1=> f1P; apply: (iffP satP) => /= allf1 => [[v]|].
  apply/f1P; case: satP => // notf1x; case: allf1; apply/ExP=> //.
  by exists v; rewrite set_val.
by case/ExP=> //= v []; apply/satP; rewrite set_val; apply/f1P.
Qed.

Definition gen_sat e f := GRing.sat (gen_env e) (gen_form (GRing.to_rform f)).

Lemma gen_satP : GRing.DecidableField.axiom gen_sat.
Proof.
move=> e f; have [tor rto] := GRing.to_rformP e f.
exact: (iffP (sat_gen_form e (GRing.to_rform_rformula f))).
Qed.

Definition gen_decFieldMixin := DecFieldMixin gen_satP.

Canonical Structure gen_decFieldType :=
  Eval hnf in DecFieldType FA gen_decFieldMixin.

End DecideGenField.

Section FiniteGenField.

Variables (F : finFieldType) (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variables (rG : mx_representation F G n) (A : 'M[F]_n).
Hypotheses (irrG : mx_irreducible rG) (cGA : centgmx rG A).
Notation FA := (gen_of irrG cGA).

Definition gen_countMixin := [countMixin of FA by <:].
Canonical Structure gen_countType := Eval hnf in CountType FA gen_countMixin.
Canonical Structure gen_subCountType := Eval hnf in [subCountType of FA].
Definition gen_finMixin := [finMixin of FA by <:].
Canonical Structure gen_finType := Eval hnf in FinType FA gen_finMixin.
Canonical Structure gen_subFinType := Eval hnf in [subFinType of FA].
Canonical Structure gen_finZmodType := Eval hnf in [finZmodType of FA].
Canonical Structure gen_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of FA for +%R].
Canonical Structure gen_finGroupType :=
  Eval hnf in [finGroupType of FA for +%R].
Canonical Structure gen_finRingType := Eval hnf in [finRingType of FA].
Canonical Structure gen_finComRingType := Eval hnf in [finComRingType of FA].
Canonical Structure gen_finUnitRingType := Eval hnf in [finUnitRingType of FA].
Canonical Structure gen_finComUnitRingType :=
   Eval hnf in [finComUnitRingType of FA].
Canonical Structure gen_finIdomainType := Eval hnf in [finIdomainType of FA].
Canonical Structure gen_finFieldType := Eval hnf in [finFieldType of FA].

Lemma card_gen : #|{:FA}| = (#|F| ^ degree_mxminpoly A)%N.
Proof. by rewrite card_sub card_matrix mul1n. Qed.

End FiniteGenField.

End MatrixGenField.

Canonical Structure MatrixGenField.gen_subType.
Canonical Structure MatrixGenField.gen_eqType.
Canonical Structure MatrixGenField.gen_choiceType.
Canonical Structure MatrixGenField.gen_countType.
Canonical Structure MatrixGenField.gen_subCountType.
Canonical Structure MatrixGenField.gen_finType.
Canonical Structure MatrixGenField.gen_subFinType.
Canonical Structure MatrixGenField.gen_zmodType.
Canonical Structure MatrixGenField.gen_finZmodType.
Canonical Structure MatrixGenField.gen_baseFinGroupType.
Canonical Structure MatrixGenField.gen_finGroupType.
Canonical Structure MatrixGenField.gen_ringType.
Canonical Structure MatrixGenField.gen_finRingType.
Canonical Structure MatrixGenField.gen_comRingType.
Canonical Structure MatrixGenField.gen_finComRingType.
Canonical Structure MatrixGenField.gen_unitRingType.
Canonical Structure MatrixGenField.gen_finUnitRingType.
Canonical Structure MatrixGenField.gen_comUnitRingType.
Canonical Structure MatrixGenField.gen_finComUnitRingType.
Canonical Structure MatrixGenField.gen_idomainType.
Canonical Structure MatrixGenField.gen_finIdomainType.
Canonical Structure MatrixGenField.gen_fieldType.
Canonical Structure MatrixGenField.gen_finFieldType.
Canonical Structure MatrixGenField.gen_decFieldType.

(* Special results for representations on a finite field. In this case, the   *)
(* representation is equivalent to a morphism into the general linear group   *)
(* 'GL_n[F]. It is furthermore equivalent to a group action on the finite     *)
(* additive group of the corresponding row space 'rV_n. In addition, row      *)
(* spaces of matrices in 'M[F]_n correspond to subgroups of that vector group *)
(* (this is only surjective when F is a prime field 'F_p), with submodules    *)
(* corresponding to subgroups stabilized by the external action.              *)

Section FiniteRepr.

Variable F : finFieldType.

(* The external group action (by scaling) of the multiplicative unit group   *)
(* of the finite field, and the correspondence between additive subgroups    *)
(* of row vectors that are stable by this action, and the matrix row spaces. *)
Section ScaleAction.

Variables m n : nat.

Definition scale_act (A : 'M[F]_(m, n)) (a : {unit F}) := val a *m: A.
Lemma scale_actE : forall A a, scale_act A a = val a *m: A. Proof. by []. Qed.
Lemma scale_is_action : is_action setT scale_act.
Proof.
apply: is_total_action=> [A | A a b]; rewrite /scale_act ?scale1mx //.
by rewrite scalemxA mulrC.
Qed.
Canonical Structure scale_action := Action scale_is_action.
Lemma scale_is_groupAction : is_groupAction setT scale_action.
Proof.
move=> a _ /=; rewrite inE; apply/andP.
split; first by apply/subsetP=> ?; rewrite !inE.
by apply/morphicP=> u A _ _ /=; rewrite !actpermE /= /scale_act scalemx_addr.
Qed.
Canonical Structure scale_groupAction := GroupAction scale_is_groupAction.

Lemma astab1_scale_act : forall A, A != 0 -> 'C[A | scale_action] = 1%g.
Proof.
move=> A; rewrite -mxrank_eq0=> nzA; apply/trivgP; apply/subsetP=> a.
apply: contraLR; rewrite !inE -val_eqE -subr_eq0 sub1set !inE => nz_a1.
by rewrite -subr_eq0 -scaleN1mx -scalemx_addl -mxrank_eq0 eqmx_scale.
Qed.

End ScaleAction.

Local Notation "'Zm" := (scale_action _ _) (at level 0) : action_scope.

Section RowGroup.

Variable n : nat.
Local Notation rVn := 'rV[F]_n.

Definition rowg m (A : 'M[F]_(m, n)) : {set rVn} := [set u | u <= A]%MR.

Lemma mem_rowg : forall m A v, (v \in @rowg m A) = (v <= A)%MR.
Proof. by move=> m A v; rewrite inE. Qed.

Lemma rowg_group_set : forall m A, group_set (@rowg m A).
Proof.
move=> m A; apply/group_setP.
by split=> [|u v]; rewrite !inE ?subset0mx //; exact: subsetmx_add.
Qed.
Canonical Structure rowg_group m A := Group (@rowg_group_set m A).

Lemma rowg_stable : forall m (A : 'M_(m, n)), [acts setT, on rowg A | 'Zm].
Proof.
by move=> m A; apply/actsP=> a _ v; rewrite !inE eqmx_scale // -unitfE (valP a).
Qed.

Lemma rowgS : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (rowg A \subset rowg B) = (A <= B)%MR.
Proof.
move=> m1 m2 A B; apply/subsetP/idP=> sAB => [| u].
  by apply/row_subP=> i; move/(_ (row i A)): sAB; rewrite !inE row_sub => ->.
by rewrite !inE => suA; exact: subsetmx_trans sAB.
Qed.

Lemma eq_rowg : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B)%MR -> rowg A = rowg B.
Proof.
by move=> m1 m2 A B eqAB; apply/eqP; rewrite eqEsubset !rowgS !eqAB andbb.
Qed.

Lemma rowg0 : forall m, rowg (0 : 'M_(m, n)) = 1%g.
Proof.
by move=> m; apply/trivgP; apply/subsetP=> v; rewrite !inE eqmx0 subsetmx0.
Qed.

Lemma rowg1 : rowg 1%:M = setT.
Proof. by apply/setP=> x; rewrite !inE subsetmx1. Qed.

Lemma trivg_rowg : forall m (A : 'M_(m, n)), (rowg A == 1%g) = (A == 0).
Proof. by move=> m A; rewrite -subsetmx0 -rowgS rowg0 (sameP trivgP eqP). Qed.

Definition rowg_mx (L : {set rVn}) :=
  <<\matrix_i val (enum_val i : subg_of <<L>>)>>%MR.

Lemma rowgK : forall m (A : 'M_(m, n)), (rowg_mx (rowg A) :=: A)%MR.
Proof.
move=> m A; apply/eqmxP; rewrite !eqmx_gen; apply/andP; split.
  apply/row_subP=> i; rewrite rowK; case: (enum_val _) => u /=.
  by rewrite genGid inE.
apply/row_subP=> i; apply: (eq_row_sub (enum_rank (subg <<rowg A>> (row i A)))).
by rewrite rowK enum_rankK subgK //= genGid inE row_sub.
Qed.

Lemma rowg_mxS : forall L M : {set 'rV[F]_n},
  L \subset M -> (rowg_mx L <= rowg_mx M)%MR.
Proof.
move=> L M; move/genS; move/subsetP=> sLM; rewrite !eqmx_gen.
apply/row_subP=> i; rewrite rowK; case: (enum_val _) => v /=; move/sLM=> Mv.
by apply: (eq_row_sub (enum_rank (subg _ v))); rewrite rowK enum_rankK subgK.
Qed.

Lemma sub_rowg_mx : forall L : {set rVn}, L \subset rowg (rowg_mx L).
Proof.
move=> L; rewrite -gen_subG; apply/subsetP=> v Lv; rewrite inE eqmx_gen.
by apply: (eq_row_sub (enum_rank (subg _ v))); rewrite rowK enum_rankK subgK.
Qed.

Lemma stable_rowg_mxK : forall L : {group rVn},
  [acts setT, on L | 'Zm] -> rowg (rowg_mx L) = L.
Proof.
move=> L linL; apply/eqP; rewrite eqEsubset sub_rowg_mx andbT.
apply/subsetP => v; rewrite inE eqmx_gen; case/subsetmxP=> u ->{v}.
rewrite mulmx_sum_row group_prod // => i _.
rewrite rowK; case: (enum_val _) => v; rewrite /= genGid => Lv.
case: (eqVneq (u 0 i) 0) => [-> |]; first by rewrite scale0mx group1.
by rewrite -unitfE => aP; rewrite ((actsP linL) (FinRing.Unit _ aP)) ?inE.
Qed.

Lemma rowg_mx1 : rowg_mx 1%g = 0.
Proof. by apply/eqP; rewrite -subsetmx0 -(rowg0 0) rowgK subset0mx. Qed.

Lemma rowg_mx_eq0 : forall L : {group rVn}, (rowg_mx L == 0) = (L :==: 1%g).
Proof.
move=> L; rewrite -trivg_rowg; apply/idP/idP.
  by rewrite !(sameP eqP trivgP); apply: subset_trans; exact: sub_rowg_mx.
by move/eqP->; rewrite rowg_mx1 rowg0.
Qed.

Lemma rowgI : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A :&: B)%MR = rowg A :&: rowg B.
Proof. by move=> m1 m2 A B; apply/setP=> u; rewrite !inE sub_capmx. Qed.

Lemma card_rowg : forall m (A : 'M_(m, n)), #|rowg A| = (#|F| ^ \rank A)%N.
Proof.
move=> m A; rewrite -[\rank A]mul1n -card_matrix.
have injA: injective (mulmxr (row_base A)).
  move=> m'; case/row_freeP: (row_base_free A) => A' A'K.
  by apply: can_inj (mulmxr A') _ => u; rewrite /= -mulmxA A'K mulmx1.
rewrite -(card_image (injA _)); apply: eq_card => v.
by rewrite inE -(eq_row_base A); apply/subsetmxP/imageP=> [] [u]; exists u.
Qed.

Lemma rowgD : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A :+: B)%MR = (rowg A * rowg B)%g.
Proof.
move=> m1 m2 A B; apply/eqP; rewrite eq_sym eqEcard mulG_subG /= !rowgS.
rewrite gsummxSl gsummxSr -(@leq_pmul2r #|rowg A :&: rowg B|) ?cardG_gt0 //=.
by rewrite -mul_cardG -rowgI !card_rowg -!expn_add mxrank_sum_cap.
Qed.

(* An alternative proof, which avoids the counting argument.
   It's outcommented because the mem_mulg rewrite takes forever to execute.
Lemma rowgD' : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A :+: B)%MR = (rowg A * rowg B)%g.
Proof.
move=> m1 m2 A B; apply/eqP; rewrite eq_sym eqEsubset mulG_subG /= !rowgS.
rewrite gsummxSl gsummxSr; apply/subsetP=> u; rewrite !inE.
by case/sub_gsummxP=> v suvA svB; rewrite -(mulgKV v u) mem_mulg ?inE.
Qed.
*)

End RowGroup.

Variables (gT : finGroupType) (G : {group gT}) (n' : nat).
Local Notation n := n'.+1.
Variable (rG : mx_representation F G n).

Lemma GL_mx_repr : mx_repr 'GL_n[F] GLval. Proof. by []. Qed.
Canonical Structure GLrepr := MxRepresentation GL_mx_repr.

Lemma GLrepr_faithful : mx_repr_faithful GLrepr.
Proof. by apply/subsetP=> A; rewrite !inE mul1mx. Qed.

Definition reprGLm x : {'GL_n[F]} := insubd (1%g : {'GL_n[F]}) (rG x).

Lemma val_reprGLm : forall x, x \in G -> val (reprGLm x) = rG x.
Proof. by move=> x Gx; rewrite val_insubd (repr_mx_unitr rG). Qed.

Lemma comp_reprGLm : {in G, GLval \o reprGLm =1 rG}.
Proof. exact: val_reprGLm. Qed.

Lemma reprGLmM : {in G &, {morph reprGLm : x y / x * y}}%g.
Proof.
by move=> x y Gx Gy; apply: val_inj; rewrite /= !val_reprGLm ?groupM ?repr_mxM.
Qed.
Canonical Structure reprGL_morphism := Morphism reprGLmM.

Lemma ker_reprGLm : 'ker reprGLm = rker rG.
Proof.
apply/setP=> x; rewrite !inE mul1mx; case Gx: (x \in G) => //=.
by rewrite -val_eqE val_reprGLm.
Qed.

Definition mx_repr_act (u : 'rV_n) x := u *m val (reprGLm x).

Lemma mx_repr_actE : forall u x, x \in G -> mx_repr_act u x = u *m rG x.
Proof. by move=> u x Gx; rewrite /mx_repr_act val_reprGLm. Qed.

Lemma mx_repr_is_action : is_action G mx_repr_act.
Proof.
split=> [x | u x y Gx Gy]; last by rewrite /mx_repr_act -mulmxA reprGLmM.
apply: can_inj (mulmx^~ (GLval (reprGLm x))^-1) _ => u.
by rewrite mulmxK ?GL_unitmx.
Qed.
Canonical Structure mx_repr_action := Action mx_repr_is_action.

Lemma mx_repr_is_groupAction : is_groupAction setT mx_repr_action.
Proof.
move=> x Gx /=; rewrite !inE.
apply/andP; split; first by apply/subsetP=> u; rewrite !inE.
by apply/morphicP=> /= u v _ _; rewrite !actpermE /= /mx_repr_act mulmx_addl.
Qed.
Canonical Structure mx_repr_groupAction := GroupAction mx_repr_is_groupAction.

Local Notation "''MR' 'rG'" := mx_repr_action (at level 10) : action_scope.
Local Notation "''MR' 'rG'" := mx_repr_groupAction : groupAction_scope.

Lemma astab_rowg_repr : forall m (A : 'M_(m, n)),
  'C(rowg A | 'MR rG) = rstab rG A.
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
apply/subsetP/eqP=> cAx => [|u]; last first.
  by rewrite !inE mx_repr_actE //; case/subsetmxP=> u' ->; rewrite -mulmxA cAx.
apply/row_matrixP=> i; move/implyP: (cAx (row i A)).
by rewrite !inE row_sub mx_repr_actE //= row_mul; move/eqP.
Qed.

Lemma astabs_rowg_repr : forall m (A : 'M_(m, n)),
  'N(rowg A | 'MR rG) = rstabs rG A.
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //=.
apply/subsetP/idP=> nAx => [|u]; last first.
  rewrite !inE mx_repr_actE // => Au; exact: (subsetmx_trans (subsetmxMr _ Au)).
apply/row_subP=> i; move/implyP: (nAx (row i A)).
by rewrite !inE row_sub mx_repr_actE //= row_mul.
Qed.

Lemma acts_rowg : forall A, [acts G, on rowg A | 'MR rG] = submodmx rG A.
Proof. by move=> A; rewrite astabs_rowg_repr. Qed.

Lemma astab_setT_repr : 'C(setT | 'MR rG) = rker rG.
Proof. by rewrite -rowg1 astab_rowg_repr. Qed.

Lemma mx_repr_action_faithful :
  [faithful G, on setT | 'MR rG] = mx_repr_faithful rG.
Proof.
rewrite /faithful astab_setT_repr (setIidPr _) //.
by apply/subsetP=> x; case/setIdP.
Qed.

Lemma afix_repr : 'Fix_('MR rG)(G) = rowg (rfix_mx rG).
Proof.
apply/setP=> /= u; rewrite !inE.
apply/subsetP/subsetmx_rfixP=> cHu x Hx;
  by move/(_ x Hx): cHu; rewrite !inE /=; move/eqP; rewrite mx_repr_actE.
Qed.

Lemma gacent_repr : 'C_(| 'MR rG)(G) = rowg (rfix_mx rG).
Proof. by rewrite gacentE // setTI afix_repr. Qed.

End FiniteRepr.

Notation "''Zm'" := (scale_action _ _ _) (at level 0) : action_scope.
Notation "''Zm'" := (scale_groupAction _ _ _) : groupAction_scope.
Notation "''MR' rG" := (mx_repr_action rG)
  (at level 10, rG at level 8, format "''MR'  rG") : action_scope.
Notation "''MR' rG" := (mx_repr_groupAction rG) : groupAction_scope.

Definition abelem_dim' (gT : finGroupType) (E : {set gT}) :=
  (logn (pdiv #|E|) #|E|).-1.
Notation "''dim' E" := (abelem_dim' E).+1
  (at level 10, E at level 8, format "''dim'  E") : group_scope.

Notation "''rV' ( E )" := 'rV_('dim E)
  (at level 8, format "''rV' ( E )") : group_scope.
Notation "''M' ( E )" := 'M_('dim E)
  (at level 8, format "''M' ( E )") : group_scope.
Notation "''rV[' F ] ( E )" := 'rV[F]_('dim E)
  (at level 8, only parsing) : group_scope.
Notation "''M[' F ] ( E )" := 'rV[F]_('dim E)
  (at level 8, only parsing) : group_scope.

Section AbelemRepr.

Import FinRing.Theory.

Section FpMatrix.

Variables p m n : nat.
Local Notation Mmn := 'M['F_p]_(m, n).

Lemma mx_Fp_abelem : prime p -> p.-abelem [set: Mmn].
Proof.
move=> p_pr; apply/p_abelemP=> //; rewrite zmod_abelian.
split=> //= v _; rewrite FinRing.zmodXgE -scalemx_nat.
by case/andP: (char_Fp p_pr) => _; move/eqP->; rewrite scale0mx.
Qed.

Lemma mx_Fp_stable : forall L : {group Mmn}, [acts setT, on L | 'Zm].
Proof.
move=> L; apply/subsetP=> a _; rewrite !inE; apply/subsetP=> A L_A.
by rewrite inE /= /scale_act -[val _]natr_Zp scalemx_nat groupX.
Qed.

End FpMatrix.

Section FpRow.

Variables p n : nat.
Local Notation rVn := 'rV['F_p]_n.

Lemma rowg_mxK : forall L : {group rVn}, rowg (rowg_mx L) = L.
Proof. move=> L; apply: stable_rowg_mxK; exact: mx_Fp_stable. Qed.

Lemma rowg_mxSK : forall (L : {set rVn}) (M : {group rVn}),
  (rowg_mx L <= rowg_mx M)%MR = (L \subset M).
Proof.
move=> L M; apply/idP/idP; last exact: rowg_mxS.
by rewrite -rowgS rowg_mxK; apply: subset_trans; exact: sub_rowg_mx.
Qed.

End FpRow.

Variables (p : nat) (gT : finGroupType) (E : {group gT}).
Hypotheses (abelE : p.-abelem E) (ntE : E :!=: 1%g).

Let pE : p.-group E := abelem_pgroup abelE.
Let p_pr : prime p. Proof. by move/eqP: ntE; case/pgroup_1Vpr: pE => [|[]]. Qed.

Local Notation n' := (abelem_dim' (gval E)).
Local Notation n := n'.+1.
Local Notation rVn := 'rV['F_p](gval E).

Lemma dim_abelemE : n = logn p #|E|.
Proof.
have:= ntE; rewrite trivg_card1 /n'; case/p_natP: pE => [[|k] ->] // _.
by rewrite /pdiv primes_exp ?primes_prime // pfactorK.
Qed.

Lemma card_abelem_rV : #|rVn| = #|E|.
Proof.
by rewrite dim_abelemE card_matrix mul1n card_Fp // -p_part part_pnat.
Qed.

Lemma isog_abelem_rV : E \isog [set: rVn].
Proof.
by rewrite (isog_abelem_card _ abelE) cardsT card_abelem_rV mx_Fp_abelem /=.
Qed.

Let ab_rV_P := (existsP isog_abelem_rV).
Definition abelem_rV : gT -> rVn := xchoose ab_rV_P.

Local Notation ErV := abelem_rV.

Lemma abelem_rV_M : {in E &, {morph ErV : x y / (x * y)%g >-> x + y}}.
Proof. by case/misomP: (xchooseP ab_rV_P) => fM _; move/morphicP: fM. Qed.

Canonical Structure abelem_rV_morphism := Morphism abelem_rV_M.

Lemma abelem_rV_isom : isom E setT ErV.
Proof. by case/misomP: (xchooseP ab_rV_P). Qed.

Lemma abelem_rV_injm : 'injm ErV. Proof. by case/isomP: abelem_rV_isom. Qed.

Lemma abelem_rV_inj : {in E &, injective ErV}.
Proof. by apply/injmP; exact: abelem_rV_injm. Qed.

Lemma im_abelem_rV : ErV @* E = setT. Proof. by case/isomP: abelem_rV_isom. Qed.

Lemma mem_im_abelem_rV : forall u, u \in ErV @* E.
Proof. by move=> u; rewrite im_abelem_rV inE. Qed.

Lemma sub_im_abelem_rV : forall mA, subset mA (mem (ErV @* E)).
Proof.
by rewrite unlock => mA; apply/pred0P=> v /=; rewrite mem_im_abelem_rV.
Qed.
Hint Resolve mem_im_abelem_rV sub_im_abelem_rV.

Lemma abelem_rV_1 : ErV 1 = 0%R. Proof. by rewrite morph1. Qed.

Lemma abelem_rV_X : forall x i, x \in E -> ErV (x ^+ i) = i%:R *m: ErV x.
Proof. by move=> x i Ex; rewrite morphX // scalemx_nat. Qed.

Lemma abelem_rV_V : forall x, x \in E -> ErV x^-1 = - ErV x.
Proof. by move=> x Ex; rewrite morphV. Qed.

Definition rVabelem : rVn -> gT := invm abelem_rV_injm.
Canonical Structure rVabelem_morphism := [morphism of rVabelem].
Local Notation rV_E := rVabelem.

Lemma rVabelem0 : rV_E 0 = 1%g. Proof. exact: morph1. Qed.

Lemma rVabelemD : {morph rV_E : u v / u + v >-> (u * v)%g}.
Proof. by move=> u v /=; rewrite -morphM. Qed.

Lemma rVabelemN : {morph rV_E: u / - u >-> (u^-1)%g}.
Proof. by move=> u /=; rewrite -morphV. Qed.

Lemma rVabelemZ : forall m : 'F_p, {morph rV_E : u / m *m: u >-> (u ^+ m)%g}.
Proof.
by move=> m u /=; rewrite -morphX /= -?[(u ^+ m)%g]scalemx_nat ?natr_Zp.
Qed.

Lemma abelem_rV_K : {in E, cancel ErV rV_E}. Proof. exact: invmE. Qed.

Lemma rVabelemK : cancel rV_E ErV. Proof. by move=> u; rewrite invmK. Qed.

Lemma rVabelem_inj : injective rV_E. Proof. exact: can_inj rVabelemK. Qed.

Lemma rVabelem_injm : 'injm rV_E. Proof. exact: injm_invm abelem_rV_injm. Qed.

Lemma im_rVabelem : rV_E @* setT = E.
Proof. by rewrite -im_abelem_rV im_invm. Qed.

Lemma mem_rVabelem : forall u, rV_E u \in E.
Proof. by move=> u; rewrite -im_rVabelem mem_morphim. Qed.

Lemma sub_rVabelem : forall L, rV_E @* L \subset E.
Proof. by move=> L; rewrite -[_ @* L]morphimIim im_invm subsetIl. Qed.
Hint Resolve mem_rVabelem sub_rVabelem.

Lemma card_rVabelem : forall L, #|rV_E @* L| = #|L|.
Proof. by move=> L; rewrite card_injm ?rVabelem_injm. Qed.

Lemma abelem_rV_mK : forall H : {set gT}, H \subset E -> rV_E @* (ErV @* H) = H.
Proof. exact: morphim_invm abelem_rV_injm. Qed.

Lemma rVabelem_mK : forall L, ErV @* (rV_E @* L) = L.
Proof. by move=> L; rewrite morphim_invmE morphpreK. Qed.

Lemma rVabelem_minj : injective (morphim (MorPhantom rV_E)).
Proof. exact: can_inj rVabelem_mK. Qed.

Lemma rVabelemS : forall L M, (rV_E @* L \subset rV_E @* M) = (L \subset M).
Proof. by move=> L M; rewrite injmSK ?rVabelem_injm. Qed.

Lemma abelem_rV_S : forall H K : {set gT},
  H \subset E -> (ErV @* H \subset ErV @* K) = (H \subset K).
Proof. by move=> H K sHE; rewrite injmSK ?abelem_rV_injm. Qed.

Lemma sub_rVabelem_im : forall L (H : {set gT}),
  (rV_E @* L \subset H) = (L \subset ErV @* H).
Proof. by move=> L H; rewrite sub_morphim_pre ?morphpre_invm. Qed.

Lemma sub_abelem_rV_im : forall (H : {set gT}) (L : {set 'rV['F_p]_n}),
  H \subset E -> (ErV @* H \subset L) = (H \subset rV_E @* L).
Proof. by move=> H L sHE; rewrite sub_morphim_pre ?morphim_invmE. Qed.

Variable G : {group gT}.
Definition abelem_mx_fun (g : subg_of G) v := ErV ((rV_E v) ^ val g).
Definition abelem_mx of G \subset 'N(E) :=
  fun x => lin1_mx (abelem_mx_fun (subg G x)).

Hypothesis nEG : G \subset 'N(E).
Local Notation r := (abelem_mx nEG).

Lemma abelem_mx_linear_proof : forall g, linear (abelem_mx_fun g).
Proof.
rewrite /abelem_mx_fun; case=> x /=; move/(subsetP nEG)=> Nx /= m u v.
rewrite rVabelemD rVabelemZ conjMg conjXg.
by rewrite abelem_rV_M ?abelem_rV_X ?groupX ?memJ_norm // natr_Zp.
Qed.
Canonical Structure abelem_mx_linear g := LinearFun (abelem_mx_linear_proof g).

Let rVabelemJmx : forall v x, x \in G -> rV_E (v *m r x) = (rV_E v) ^ x.
Proof.
move=> v x Gx; rewrite /= mul_rV_lin1 /= /abelem_mx_fun subgK //.
by rewrite abelem_rV_K // memJ_norm // (subsetP nEG).
Qed.

Lemma abelem_mx_repr : mx_repr G r.
Proof.
split=> [|x y Gx Gy]; apply/row_matrixP=> i; apply: rVabelem_inj.
  by rewrite rowE -row1 rVabelemJmx // conjg1.
by rewrite !rowE mulmxA !rVabelemJmx ?groupM // conjgM.
Qed.
Canonical Structure abelem_repr := MxRepresentation abelem_mx_repr.
Let rG := abelem_repr.

Lemma rVabelemJ : forall v x, x \in G -> rV_E (v *m rG x) = (rV_E v) ^ x.
Proof. exact: rVabelemJmx. Qed.

Lemma abelem_rV_J : {in E & G, forall x y, ErV (x ^ y) = ErV x *m rG y}.
Proof.
by move=> x y Ex Gy; rewrite -{1}(abelem_rV_K Ex) -rVabelemJ ?rVabelemK.
Qed.

Lemma abelem_rowgJ : forall m (A : 'M_(m, n)) x,
  x \in G -> rV_E @* rowg (A *m rG x) = (rV_E @* rowg A) :^ x.
Proof.
move=> m A x Gx; apply: (canRL (conjsgKV _)); apply/setP=> y.
rewrite mem_conjgV !morphim_invmE !inE memJ_norm ?(subsetP nEG) //=.
case Ey: (y \in E) => //=; rewrite abelem_rV_J //.
by rewrite subsetmxMfree // row_free_unit (repr_mx_unit rG).
Qed.

Lemma rV_abelem_sJ : forall (L : {group gT}) x,
  x \in G -> L \subset E -> ErV @* (L :^ x) = rowg (rowg_mx (ErV @* L) *m rG x).
Proof.
move=> L x Gx sLE; apply: rVabelem_minj; rewrite abelem_rowgJ //.
by rewrite rowg_mxK !morphim_invm // -(normsP nEG x Gx) conjSg.
Qed.

Lemma rstab_abelem : forall m (A : 'M_(m, n)),
  rstab rG A = 'C_G(rV_E @* rowg A).
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx : (x \in G) => //=.
apply/eqP/centP=> cAx => [u|].
  case/morphimP=> u' _; rewrite inE; case/subsetmxP=> u'' -> ->{u u'}.
  symmetry; apply/commgP; apply/conjg_fixP.
  by rewrite -rVabelemJ -?mulmxA ?cAx.
apply/row_matrixP=> i; apply: rVabelem_inj.
by rewrite row_mul rVabelemJ // /conjg -cAx ?mulKg ?mem_morphim // inE row_sub.
Qed.

Lemma rstabs_abelem : forall m (A : 'M_(m, n)),
  rstabs rG A = 'N_G(rV_E @* rowg A).
Proof.
move=> m A; apply/setP=> x; rewrite !inE; case Gx : (x \in G) => //.
by rewrite -rowgS -rVabelemS abelem_rowgJ.
Qed.

Lemma rstabs_abelem_rowg_mx : forall L : {group gT},
  L \subset E -> rstabs rG (rowg_mx (ErV @* L)) = 'N_G(L).
Proof. by move=> L sLE; rewrite rstabs_abelem rowg_mxK morphim_invm. Qed.

Lemma abelem_mx_irrP : reflect (mx_irreducible rG) (minnormal E G).
Proof.
apply: (iffP mingroupP) => [[_ minE]|irrG].
  apply/mx_irrP; split=> // U; rewrite /submodmx rstabs_abelem //.
  rewrite subsetI subxx /= -trivg_rowg.
  rewrite -(inj_eq rVabelem_minj) morphim1; set L := _ @* _ U => nLG ntL. 
  by rewrite -subset1mx -rowgS -rVabelemS -/L [L]minE ?ntL /=.
rewrite ntE; split=> // L; case/andP=> ntL nLG sLE; apply/eqP.
rewrite eqEsubset sLE -im_rVabelem sub_rVabelem_im //= -rowg_mxSK //.
move/setIidPl: nLG; rewrite -rstabs_abelem_rowg_mx //.
set U := rowg_mx _ => Umod; rewrite subsetmx_full //.
case/mx_irrP: irrG => _ -> //; first by rewrite /submodmx Umod.
apply: contra ntL; rewrite rowg_mx_eq0 !(sameP eqP trivgP).
by rewrite sub_abelem_rV_im // morphim1.
Qed.

(* Temporarily out-commented, as this requires > 20s processing time
Lemma rfix_abelem : forall H : {group gT},
  H \subset G -> (rfix_mx rG H :=: rowg_mx (ErV @* 'C_E(H)))%MR.
Proof.
move=> H; move/subsetP=> sHG; apply/eqmxP; apply/andP; split.
  rewrite -rowgS rowg_mxK -sub_rVabelem_im // subsetI sub_rVabelem /=.
  apply/centsP=> y; case/morphimP=> v _; rewrite inE => cHv ->{y} x Hx.
  apply/commgP; apply/conjg_fixP; rewrite /= -rVabelemJ ?sHG //.
  by rewrite (subsetmx_rfixP _ _ _ cHv).
rewrite eqmx_gen; apply/subsetmx_rfixP=> x Hx.
apply/row_matrixP=> i; rewrite row_mul rowK; case: (enum_val i) => /= v.
rewrite genGid; case/morphimP=> z Ez; case/setIP=> _ cHz -> {v}.
by rewrite -abelem_rV_J ?sHG // conjgE (centP cHz) ?mulKg.
Qed.
*)

Lemma rker_abelem : rker rG = 'C_G(E).
Proof. by rewrite /rker rstab_abelem rowg1 im_rVabelem. Qed.

Lemma abelem_repr_faithful : 'C_G(E) = 1%g -> mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_abelem => ->. Qed.
  
End AbelemRepr.
