Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div choice.
Require Import fintype tuple finfun bigops prime binomial ssralg poly finset.
Require Import groups morphisms automorphism normal perm finalg action gprod.
Require Import zmodp matrix commutators cyclic center pgroups gseries.
Require Import sylow abelian maximal.

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
(* mxmodule rG U == the row-space of the n x n matrix U is a module         *)
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
(* mx_irreducible rG == the representation r of G is not reducible; as it   *)
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

(* to ssrbool.v *)
Definition not_false := not_false_is_true.

Lemma contraT : forall b, (~~ b -> false) -> b. Proof. by case=> // ->. Qed.

Lemma wlog_neg : forall b, (~~ b -> b) -> b. Proof. by case=> // ->. Qed.

Definition classically P := forall b : bool, (P -> b) -> b.

Lemma classicP : forall P : Prop, classically P <-> ~ ~ P.
Proof.
move=> P; split=> [cP nP | nnP [] // nP]; last by case nnP; move/nP.
by have: P -> false; [move/nP | move/cP].
Qed.

Lemma classic_bind : forall P Q,
  (P -> classically Q) -> (classically P -> classically Q).
Proof. by move=> P Q IH IH_P b IH_Q; apply: IH_P; move/IH; exact. Qed.

Lemma classic_EM : forall P, classically ({P} + {~ P}).
Proof.
by move=> P [] // IH; apply IH; right => ?; apply: not_false (IH _); left.
Qed.

Lemma classic_imply : forall P Q, (P -> classically Q) -> classically (P -> Q).
Proof.
move=> P Q IH [] // notPQ; apply notPQ; move/IH=> hQ; case: not_false.
by apply: hQ => hQ; case: not_false; exact: notPQ.
Qed.

Lemma classic_pick : forall T P,
  classically ({x : T | P x} + (forall x, ~ P x)).
Proof.
move=> T P [] // IH; apply IH; right=> x Px; case: not_false.
by apply: IH; left; exists x.
Qed.


(* to seq.v *)
Section Subseq.

Variable T : eqType.
Implicit Type s : seq T.

Fixpoint subseq s1 s2 :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then subseq (if x == y then s1' else s1) s2' else true
  else s1 == [::].

Lemma sub0seq : forall s, subseq [::] s. Proof. by case. Qed.

Lemma subseq0 : forall s, subseq s [::] = (s == [::]). Proof. by []. Qed.

Lemma subseqP : forall s1 s2,
  reflect (exists2 m, size m = size s2 & s1 = mask m s2) (subseq s1 s2).
Proof.
move=> s1 s2; elim: s2 s1 => [|y s2 IHs2] [|x s1].
- by left; exists [::].
- by right; do 2!case.
- by left; exists (nseq (size s2).+1 false); rewrite ?size_nseq //= mask_false.
apply: {IHs2}(iffP (IHs2 _)) => [] [m sz_m def_s1].
  by exists ((x == y) :: m); rewrite /= ?sz_m // -def_s1; case: eqP => // ->.
case: eqP => [_ | ne_xy]; last first.
  by case: m def_s1 sz_m => [|[] m] // [] // -> [<-]; exists m. 
pose i := index true m; have def_m_i: take i m = nseq (size (take i m)) false.
  apply/all_pred1P; apply/(all_nthP true) => j.
  rewrite size_take ltnNge leq_minl negb_or -ltnNge; case/andP=> lt_j_i _.
  rewrite nth_take //= -negb_add addbF -addbT -negb_eqb.
  by rewrite [_ == _](before_find _ lt_j_i).
have lt_i_m: i < size m.
  rewrite ltnNge; apply/negP=> le_m_i; rewrite take_oversize // in def_m_i.
  by rewrite def_m_i mask_false in def_s1.
rewrite size_take lt_i_m in def_m_i.
exists (take i m ++ drop i.+1 m).
  rewrite size_cat size_take size_drop lt_i_m.
  by rewrite sz_m in lt_i_m *; rewrite subnKC.
rewrite {s1 def_s1}[s1](congr1 behead def_s1).
rewrite -[s2](cat_take_drop i) -{1}[m](cat_take_drop i) {}def_m_i -cat_cons.
have sz_i_s2: size (take i s2) = i by apply: size_takel; rewrite sz_m in lt_i_m.
rewrite lastI cat_rcons !mask_cat ?size_nseq ?size_belast ?mask_false //=.
by rewrite (drop_nth true) // nth_index -?index_mem.
Qed.

Lemma subseq_trans : transitive subseq.
Proof.
move=> s1 s2 s3; case/subseqP=> m2 _ ->; case/subseqP=> m1 _ ->{s1 s2}.
elim: s3 m2 m1 => [|x s IHs] m2 m1; first by rewrite !mask0.
case: m1 => [|[] m1]; first by rewrite mask0.
  case: m2 => [|[] m2] //; first by rewrite /= eqxx IHs.
  case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
  by exists (false :: m); rewrite //= sz_m.
case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
by exists (false :: m); rewrite //= sz_m.
Qed.

Lemma subseq_refl : forall s, subseq s s.
Proof. by elim=> //= x s IHs; rewrite eqxx. Qed.
Hint Resolve subseq_refl.

Lemma subseq_cat : forall s1 s2 s3 s4,
  subseq s1 s3 -> subseq s2 s4 -> subseq (s1 ++ s2) (s3 ++ s4).
Proof.
move=> s1 s2 s3 s4; case/subseqP=> m1 sz_m1 ->; case/subseqP=> m2 sz_m2 ->.
by apply/subseqP; exists (m1 ++ m2); rewrite ?size_cat ?mask_cat ?sz_m1 ?sz_m2.
Qed.

Lemma mem_subseq : forall s1 s2, subseq s1 s2 -> {subset s1 <= s2}.
Proof. by move=> s1 s2; case/subseqP=> m _ -> x; exact: mem_mask. Qed.

Lemma size_subseq : forall s1 s2, subseq s1 s2 -> size s1 <= size s2.
Proof.
by move=> s1 s2; case/subseqP=> m sz_m ->; rewrite size_mask -sz_m ?count_size.
Qed.

Lemma size_subseq_leqif : forall s1 s2,
  subseq s1 s2 -> size s1 <= size s2 ?= iff (s1 == s2).
Proof.
move=> s1 s2 sub12; split; first exact: size_subseq.
apply/idP/eqP=> [|-> //]; case/subseqP: sub12 => m sz_m ->{s1}.
rewrite size_mask -sz_m // -all_count -(eq_all andbT).
by move/(@all_pred1P _ true)->; rewrite sz_m mask_true.
Qed.

Lemma subseq_cons : forall s x, subseq s (x :: s).
Proof. by move=> s x; exact: (@subseq_cat [::] s [:: x]). Qed.

Lemma subseq_rcons : forall s x, subseq s (rcons s x).
Proof. by move=> s x; rewrite -{1}[s]cats0 -cats1 subseq_cat. Qed.

Lemma subseq_uniq : forall s1 s2, subseq s1 s2 -> uniq s2 -> uniq s1.
Proof. by move=> s1 s2; case/subseqP=> m _ -> Us2; exact: mask_uniq. Qed.

End Subseq.

Prenex Implicits subseq.
Implicit Arguments subseqP [T s1 s2].

Hint Resolve subseq_refl.

(* to fintype.v *)
Lemma lift_max : forall m (i : 'I_m), lift ord_max i = i :> nat.
Proof. by move=> m i; rewrite /= /bump leqNgt ltn_ord. Qed.

Lemma lift0 : forall m (i : 'I_m), lift ord0 i = i.+1 :> nat. Proof. by []. Qed.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* to matrix.v *)

Section MoreMatrix.

Variable F : fieldType.

Lemma rV_eqP : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  reflect (forall u : 'rV_n, (u <= A) = (u <= B))%MS (A == B)%MS.
Proof.
move=> m1 m2 ? A B; apply: (iffP idP) => [eqAB u | eqAB].
  by rewrite (eqmxP eqAB).
by apply/andP; split; apply/rV_subP=> u; rewrite eqAB.
Qed.

Lemma eqmx0P : forall m n (A : 'M[F]_(m, n)),
  reflect (A = 0) (A == (0 : 'M_n))%MS.
Proof. by move=> m n A; rewrite subsetmx0 subset0mx andbT; exact: eqP. Qed.

Lemma eqmx_eq0 : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A :=: B)%MS -> (A == 0) = (B == 0).

Proof. by move=> m1 m2 n A B eqAB; rewrite -!mxrank_eq0 eqAB. Qed.

Lemma addsmx_addKl : forall n m1 m2 (A : 'M[F]_(m1, n)) (B C : 'M_(m2, n)),
  (B <= A)%MS -> (A + (B + C)%R :=: A + C)%MS.
Proof.
move=> n m1 m2 A B C sBA; apply/eqmxP; rewrite !addsmx_sub !addsmxSl.
by rewrite -{3}[C](addKr B) !addmx_sub_adds ?eqmx_opp.
Qed.

Lemma addsmx_addKr : forall n m1 m2 (A B : 'M[F]_(m1, n)) (C : 'M_(m2, n)),
  (B <= C)%MS -> ((A + B)%R + C :=: A + C)%MS.
Proof.
by move=> n m1 m2 A B C; rewrite -!(addsmxC C) addrC; exact: addsmx_addKl.
Qed.

Lemma addsmx_idPr : forall n m1 m2 (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)),
  reflect (A + B :=: B)%MS (A <= B)%MS.
Proof.
move=> n m1 m2 A B; have:= @eqmxP _ _ _ _ (A + B)%MS B.
by rewrite addsmxSr addsmx_sub subsetmx_refl !andbT.
Qed.

Lemma addsmx_idPl : forall n m1 m2 (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)),
  reflect (A + B :=: A)%MS (B <= A)%MS.
Proof. by move=> n m1 m2 A B; rewrite addsmxC; exact: addsmx_idPr. Qed.

Lemma capmx_idPr : forall n m1 m2 (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :&: B :=: B)%MS (B <= A)%MS.
Proof.
move=> n m1 m2 A B; have:= @eqmxP _ _ _ _ (A :&: B)%MS B.
by rewrite capmxSr sub_capmx subsetmx_refl !andbT.
Qed.

Lemma capmx_idPl : forall n m1 m2 (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)),
  reflect (A :&: B :=: A)%MS (A <= B)%MS.
Proof. by move=> n m1 m2 A B; rewrite capmxC; exact: capmx_idPr. Qed.

Lemma kermx_eq0 : forall n m (A : 'M[F]_(m, n)),
  (kermx A == 0) = row_free A.
Proof.
move=> n m A; rewrite -mxrank_eq0 mxrank_ker subn_eq0.
by rewrite /row_free eqn_leq rank_leq_row.
Qed.

Lemma row_free_inj : forall m n p (A : 'M[F]_(n, p)),
  row_free A -> injective ((@mulmx _ m n p)^~ A).
Proof.
move=> m n p A; case/row_freeP=> A' AK; apply: can_inj (mulmx^~ A') _ => B.
by rewrite -mulmxA AK mulmx1.
Qed.

Lemma row_full_inj : forall m n p (A : 'M[F]_(m, n)),
  row_full A -> injective (@mulmx _ m n p A).
Proof.
move=> m n p A; case/row_fullP=> A' A'K; apply: can_inj (mulmx A') _ => B.
by rewrite mulmxA A'K mul1mx.
Qed.

Lemma mxrank_injP : forall m n p (A : 'M[F]_(m, n)) (f : 'M[F]_(n, p)),
  reflect (\rank (A *m f) = \rank A) ((A :&: kermx f)%MS == 0).
Proof.
move=> m n p A f; rewrite -mxrank_eq0 -(eqn_addl (\rank (A *m f))).
rewrite addn0 mxrank_mul_ker eq_sym; exact: eqP.
Qed.

Definition ltmx m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)) :=
  (A <= B)%MS && ~~ (B <= A)%MS.

Local Notation "A < B" := (ltmx A B) : matrix_set_scope.

Lemma ltmxE : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A < B)%MS = ((A <= B)%MS && ~~ (B <= A)%MS).
Proof. by []. Qed.

Lemma ltmxEneq : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A < B)%MS = (A <= B)%MS && ~~ (A == B)%MS.
Proof. by move=> m1 m2 n A B; apply: andb_id2l => ->. Qed.

Lemma subsetmxElt : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A <= B)%MS = (A == B)%MS || (A < B)%MS.
Proof. by move=> m1 m2 n A B; rewrite -andb_orr orbN andbT. Qed.

Lemma ltmxErank : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A < B)%MS = (A <= B)%MS && (\rank A < \rank B).
Proof.
move=> m1 m2 n A B; apply: andb_id2l => sAB.
by rewrite (ltn_leqif (mxrank_leqif_sup sAB)).
Qed.

Lemma rank_ltmx : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A < B)%MS -> \rank A < \rank B.
Proof. by move=> m1 m2 n A B; rewrite ltmxErank; case/andP. Qed.

Lemma lt0mx : forall m n (A : 'M[F]_(m, n)), ((0 : 'M_n) < A)%MS = (A != 0).
Proof. by move=> m n A; rewrite /ltmx subset0mx subsetmx0. Qed.

Lemma ltmx0 : forall m n (A : 'M[F]_(m, n)), (A < (0 : 'M_n))%MS = false.
Proof. by move=> m n A; rewrite /ltmx subset0mx andbF. Qed.

Lemma ltmx1 : forall m n (A : 'M[F]_(m, n)), (A < 1%:M)%MS = ~~ row_full A.
Proof. by move=> m n A; rewrite /ltmx subset1mx subsetmx1. Qed.

Lemma lt1mx : forall m n (A : 'M[F]_(m, n)), (1%:M < A)%MS = false.
Proof. by move=> m n A; rewrite /ltmx subsetmx1 andbF. Qed.

Lemma ltmxW : forall m1 m2 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
  (A < B)%MS -> (A <= B)%MS.
Proof. by move=> m1 m2 n A B; case/andP. Qed.

Lemma ltmx_sub_trans : forall m1 m2 m3 n
  (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)) (C : 'M[F]_(m3, n)),
  (A < B)%MS -> (B <= C)%MS -> (A < C)%MS.
Proof.
move=> m1 m2 m3 n A B C; case/andP=> sAB ltAB sBC.
rewrite ltmxE (subsetmx_trans sAB) //.
by apply: contra ltAB; exact: subsetmx_trans.
Qed.

Lemma sub_ltmx_trans : forall m1 m2 m3 n
  (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)) (C : 'M[F]_(m3, n)),
  (A <= B)%MS -> (B < C)%MS -> (A < C)%MS.
Proof.
move=> m1 m2 m3 n A B C sAB; case/andP=> sBC ltBC.
rewrite ltmxE (subsetmx_trans sAB) //.
by apply: contra ltBC => sCA; exact: subsetmx_trans sAB.
Qed.

Lemma ltmx_trans : forall m n, transitive (@ltmx m m n).
Proof. by move=> m n A B C; move/ltmxW; exact: sub_ltmx_trans. Qed.

Lemma ltmx_irrefl : forall m n, irreflexive (@ltmx m m n).
Proof. by move=> m n A; rewrite /ltmx subsetmx_refl andbF. Qed.

Lemma lt_eqmx : forall m1 m2 m3 n (A : 'M[F]_(m1, n)) (B : 'M[F]_(m2, n)),
    (A :=: B)%MS ->
  forall C : 'M_(m3, n), (((A < C) = (B < C))%MS * ((C < A) = (C < B))%MS)%type.
Proof. by move=> m1 m2 m3 n A B eqAB C; rewrite /ltmx !eqAB. Qed.

End MoreMatrix.

Arguments Scope ltmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Prenex Implicits ltmx.

Notation "A < B" := (ltmx A B) : matrix_set_scope.
Notation "A < B <= C" := (ltmx A B && subsetmx B C) : matrix_set_scope.
Notation "A <= B < C" := (subsetmx A B && ltmx B C) : matrix_set_scope.
Notation "A < B < C" := (ltmx A B && ltmx B C) : matrix_set_scope.

Implicit Arguments rV_eqP [F m1 m2 n A B].
Implicit Arguments eqmx0P [F m n A].
Implicit Arguments addsmx_idPr [F m1 m2 n A B].
Implicit Arguments addsmx_idPl [F m1 m2 n A B].
Implicit Arguments capmx_idPr [F m1 m2 n A B].
Implicit Arguments capmx_idPl [F m1 m2 n A B].

Section MapLtmx.

Variables (aF rF : fieldType) (f : aF -> rF) (fRM : GRing.morphism f).

Lemma ltmx_map : forall m1 m2 n (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (map_mx f A < map_mx f B)%MS = (A < B)%MS.
Proof. by move=> m1 m2 n A B; rewrite /ltmx !subsetmx_map. Qed.

End MapLtmx.

(* end exports *)

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

Lemma mxvec_eq0 : forall A : 'M[R]_(m1, n1), (mxvec A == 0) = (A == 0).
Proof. by move=> A; rewrite -[A == 0](inj_eq (can_inj mxvecK)) linear0. Qed.

Lemma vec_mx_eq0 : forall v : 'rV[R]_(m1 * n1), (vec_mx v == 0) = (v == 0).
Proof. by move=> v; rewrite -(inj_eq (can_inj vec_mxK)) linear0. Qed.

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

Section LinMul.

Variables (R : comRingType) (m n p : nat).

Definition lin_mul_row u : 'M[R]_(m * n, n) := lin1_mx (mulmx u \o vec_mx).
Definition lin_mulmx A : 'M[R]_(n * p, m * p) := lin_mx (mulmx A).
Definition lin_mulmxr A : 'M[R]_(m * n, m * p) := lin_mx (mulmxr A).

Fact lin_mul_row_linear_proof : linear lin_mul_row.
Proof.
move=> a u v; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin1 /=.
by rewrite [_ *m _](linearP (mulmxr_linear _ _)).
Qed.
Canonical Structure lin_mul_row_linear := LinearFun lin_mul_row_linear_proof.

Lemma mul_vec_lin_row : forall A u, mxvec A *m lin_mul_row u = u *m A.
Proof. by move=> A u; rewrite mul_rV_lin1 /= mxvecK. Qed.

Fact lin_mulmx_linear_proof : linear lin_mulmx.
Proof.
move=> a A B; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin /=.
by rewrite [_ *m _](linearP (mulmxr_linear _ _)) linearP.
Qed.
Canonical Structure lin_mulmx_linear := LinearFun lin_mulmx_linear_proof.

Fact lin_mulmxr_linear_proof : linear lin_mulmxr.
Proof.
move=> a A B; apply/row_matrixP=> i; rewrite linearP /= !rowE !mul_rV_lin /=.
by rewrite !linearP.
Qed.
Canonical Structure lin_mulmxr_linear := LinearFun lin_mulmxr_linear_proof.

End LinMul.

Implicit Arguments lin_mul_row [R m n].
Implicit Arguments lin_mulmx [R m n p].
Implicit Arguments lin_mulmxr [R m n p].
Prenex Implicits lin_mul_row lin_mulmx lin_mulmxr.

(* Characterizing scalar matrices.                                            *)
Section ScalarMatrix.

Variables (R : ringType) (n : nat).

Definition is_scalar_mx (A : 'M[R]_n) :=
  if insub 0%N is Some i then A == (A i i)%:M else true.

Lemma is_scalar_mxP : forall A, reflect (exists a, A = a%:M) (is_scalar_mx A).
Proof.
rewrite /is_scalar_mx; case: insubP => [i _ _ A | ].
  by apply: (iffP eqP) => [|[a ->]]; [exists (A i i) | rewrite mxE eqxx].
by case: n => // _ A; left; exists 0; rewrite scalar_mx0 [A]flatmx0.
Qed.

Lemma scalar_mx_is_scalar : forall a, is_scalar_mx a%:M.
Proof. by move=> a; apply/is_scalar_mxP; exists a. Qed.

Lemma mx0_is_scalar : is_scalar_mx 0.
Proof. by rewrite -scalar_mx0 scalar_mx_is_scalar. Qed.

End ScalarMatrix.

Implicit Arguments is_scalar_mxP [R n A].

Notation "''A_' ( m , n )" := 'M_(m, n ^ 2)
  (at level 8, format "''A_' ( m ,  n )") : type_scope.

Notation "''A_' ( n )" := 'A_(n ^ 2, n)
  (at level 8, only parsing) : type_scope.

Notation "''A_' n" := 'A_(n)
  (at level 8, n at next level, format "''A_' n") : type_scope.

Notation "'A [ F ]_ ( m , n )" := 'M[F]_(m, n ^ 2)
  (at level 8, only parsing) : type_scope.

Notation "'A [ F ]_ ( n )" := 'A[F]_(n ^ 2, n)
  (at level 8, only parsing) : type_scope.

Notation "'A [ F ]_ n" := 'A[F]_(n)
  (at level 8, n at level 2, only parsing) : type_scope.

Section MatrixAlgebra.

Variables F : fieldType.

Local Notation "A \in R" := (@subsetmx F _ _ _ (mxvec A) R).

Lemma mem0mx : forall m n (R : 'A_(m, n)), 0 \in R.
Proof. by move=> m n R; rewrite linear0 subset0mx. Qed.

Lemma memmx0 : forall n A, (A \in (0 : 'A_n)) -> A = 0.
Proof. by move=> m A; rewrite subsetmx0 mxvec_eq0; move/eqP. Qed.

Lemma memmx1 : forall n (A : 'M_n), (A \in mxvec 1%:M) = is_scalar_mx A.
Proof.
move=> n A; apply/sub_rVP/is_scalar_mxP=> [[a] | [a ->]].
  by rewrite -linearZ scale_scalar_mx mulr1; move/(can_inj mxvecK); exists a.
by exists a; rewrite -linearZ scale_scalar_mx mulr1.
Qed.

Lemma memmx_subP : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (forall A, A \in R1 -> A \in R2) (R1 <= R2)%MS.
Proof.
move=> m1 m2 n R1 R2.
apply: (iffP idP) => [sR12 A R1_A | sR12]; first exact: subsetmx_trans sR12.
by apply/rV_subP=> vA; rewrite -(vec_mxK vA); exact: sR12.
Qed.
Implicit Arguments memmx_subP [m1 m2 n R1 R2].

Lemma memmx_eqP : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (forall A, (A \in R1) = (A \in R2)) (R1 == R2)%MS.
Proof.
move=> m1 m2 n R1 R2.
apply: (iffP eqmxP) => [eqR12 A | eqR12]; first by rewrite eqR12.
by apply/eqmxP; apply/rV_eqP=> vA; rewrite -(vec_mxK vA) eqR12.
Qed.
Implicit Arguments memmx_eqP [m1 m2 n R1 R2].

Lemma memmx_addsP : forall m1 m2 n A (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (exists2 A2, A - A2 \in R1 & A2 \in R2) (A \in R1 + R2)%MS.
Proof.
move=> m1 m2 n A R1 R2.
apply: (iffP sub_addsmxP) => [[v2 Rv1 Rv2] | [A2 R1_A1 R2_A2]].
  by exists (vec_mx v2); rewrite ?linear_sub /= vec_mxK.
by exists (mxvec A2); rewrite -?linear_sub.
Qed.
Implicit Arguments memmx_addsP [m1 m2 n A R1 R2].

Lemma memmx_sumsP : forall (I : finType) (P : pred I) n (A : 'M_n) R_,
  reflect (exists2 A_, A = \sum_(i | P i) A_ i & forall i, A_ i \in R_ i)
          (A \in \sum_(i | P i) R_ i)%MS.
Proof.
move=> I P n A R_.
apply: (iffP sub_sumsmxP) => [[C defA] | [A_ -> R_A] {A}].
  exists (fun i => vec_mx (C i *m R_ i)) => [|i].
    by rewrite -linear_sum -defA /= mxvecK.
  by rewrite vec_mxK subsetmxMl.
exists (fun i => mxvec (A_ i) *m pinvmx (R_ i)).
by rewrite linear_sum; apply: eq_bigr => i _; rewrite mulmxKpV.
Qed.
Implicit Arguments memmx_sumsP [I P n A R_].

Lemma has_non_scalar_mxP : forall m n (R : 'A_(m, n)), 
    (1%:M \in R)%MS ->
  reflect (exists2 A, A \in R & ~~ is_scalar_mx A)%MS (1 < \rank R).
Proof.
move=> m n; case: (posnP n) => [-> | n_gt0] R; set S := mxvec _ => sSR.
  by rewrite [R]thinmx0 mxrank0; right; case; rewrite /is_scalar_mx ?insubF.
have rankS: \rank S = 1%N.
  apply/eqP; rewrite eqn_leq rank_leq_row lt0n mxrank_eq0 mxvec_eq0.
  by rewrite -mxrank_eq0 mxrank1 -lt0n.
rewrite -{2}rankS (ltn_leqif (mxrank_leqif_sup sSR)).
apply: (iffP idP) => [|[A sAR]].
  case/row_subPn=> i; rewrite -[row i R]vec_mxK memmx1.
  by set A := vec_mx _ => nsA; exists A; rewrite // vec_mxK row_sub.
by rewrite -memmx1; apply: contra; exact: subsetmx_trans.
Qed.

Definition mulsmx m1 m2 n (R1 : 'A[F]_(m1, n)) (R2 : 'A_(m2, n)) :=
  (\sum_i <<R1 *m lin_mx (mulmxr (vec_mx (row i R2)))>>)%MS.

Arguments Scope mulsmx
  [nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].

Local Notation "R1 * R2" := (mulsmx R1 R2) : matrix_set_scope.

Lemma genmx_muls : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  <<(R1 * R2)%MS>>%MS = (R1 * R2)%MS.
Proof.
by move=> *; rewrite genmx_sums; apply: eq_bigr => i; rewrite genmx_id.
Qed.

Lemma mem_mulsmx : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) A1 A2,
  (A1 \in R1 -> A2 \in R2 -> A1 *m A2 \in R1 * R2)%MS.
Proof.
move=> m1 m2 n R1 R2 A1 A2 R_A1 R_A2.
rewrite -[A2]mxvecK; case/subsetmxP: R_A2 => a ->{A2}.
rewrite mulmx_sum_row !linear_sum summx_sub // => i _.
rewrite !linearZ scalemx_sub {a}//= (sumsmx_sup i) // genmxE.
rewrite -[A1]mxvecK; case/subsetmxP: R_A1 => a ->{A1}.
by apply/subsetmxP; exists a; rewrite mulmxA mul_rV_lin.
Qed.

Lemma mulsmx_subP : forall m1 m2 m n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
                    forall (R : 'A_(m, n)),
  reflect (forall A1 A2, A1 \in R1 -> A2 \in R2 -> A1 *m A2 \in R)
          (R1 * R2 <= R)%MS.
Proof.
move=> m1 m2 m n R1 R2 R; apply: (iffP memmx_subP) => [sR12R * | sR12R A].
  by rewrite sR12R ?mem_mulsmx.
case/memmx_sumsP=> A_ -> R_A; rewrite linear_sum summx_sub //= => j _.
rewrite (subsetmx_trans (R_A _)) // genmxE; apply/row_subP=> i.
by rewrite row_mul mul_rV_lin sR12R ?vec_mxK ?row_sub.
Qed.
Implicit Arguments mulsmx_subP [m1 m2 m n R1 R2 R].

Lemma mulsmxS : forall m1 m2 m3 m4 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
                forall (R3 : 'A_(m3, n)) (R4 : 'A_(m4, n)),
  (R1 <= R3 -> R2 <= R4 -> R1 * R2 <= R3 * R4)%MS.
Proof.
move=> m1 m2 m3 m4 n R1 R2 R3 R4 sR13 sR24.
apply/mulsmx_subP=> A1 A2 R_A1 R_A2.
by apply: mem_mulsmx; [exact: subsetmx_trans sR13 | exact: subsetmx_trans sR24].
Qed.

Lemma muls_eqmx : forall m1 m2 m3 m4 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
                  forall (R3 : 'A_(m3, n)) (R4 : 'A_(m4, n)),
  (R1 :=: R3 -> R2 :=: R4 -> R1 * R2 = R3 * R4)%MS.
Proof.
move=> m1 m2 m3 m4 n R1 R2 R3 R4 eqR13 eqR24.
rewrite -(genmx_muls R1 R2) -(genmx_muls R3 R4); apply/genmxP.
by rewrite !mulsmxS ?eqR13 ?eqR24.
Qed.

Lemma mulsmxP : forall m1 m2 n A (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
  reflect (exists2 A1, forall i, A1 i \in R1 & exists2 A2, forall i, A2 i \in R2
           & A = \sum_(i < n ^ 2) A1 i *m A2 i)
          (A \in R1 * R2)%MS.
Proof.
move=> m1 m2 n A R1 R2.
apply: (iffP idP) => [R_A|[A1 R_A1 [A2 R_A2 ->{A}]]]; last first.
  by rewrite linear_sum summx_sub // => i _; rewrite mem_mulsmx.
have{R_A}: (A \in R1 * <<R2>>)%MS.
  by apply: memmx_subP R_A; rewrite mulsmxS ?genmxE.
case/memmx_sumsP=> A_ -> R_A; pose A2_ i := vec_mx (row i <<R2>>%MS).
pose A1_ i := mxvec (A_ i) *m pinvmx (R1 *m lin_mx (mulmxr (A2_ i))) *m R1.
exists (vec_mx \o A1_) => [i|]; first by rewrite vec_mxK subsetmxMl.
exists A2_ => [i|]; first by rewrite vec_mxK -(genmxE R2) row_sub.
apply: eq_bigr => i _; rewrite -[_ *m _](mx_rV_lin (mulmxr_linear _ _)).
by rewrite -mulmxA mulmxKpV ?mxvecK // -(genmxE (_ *m _)) R_A.
Qed.
Implicit Arguments mulsmxP [m1 m2 n A R1 R2].

Lemma mulsmxA : forall m1 m2 m3 n (R1 : 'A_(m1, n)),
                forall (R2 : 'A_(m2, n)) (R3 : 'A_(m3, n)),
  (R1 * (R2 * R3) = R1 * R2 * R3)%MS.
Proof.
move=> m1 m2 m3 n R1 R2 R3; rewrite -(genmx_muls (_ * _)%MS) -genmx_muls.
apply/genmxP; apply/andP; split.
  apply/mulsmx_subP=> A1 A23 R_A1; case/mulsmxP=> A2 R_A2 [A3 R_A3 ->{A23}].
  by rewrite !linear_sum summx_sub //= => i _; rewrite mulmxA !mem_mulsmx.
apply/mulsmx_subP=> A12 A3; case/mulsmxP=> A1 R_A1 [A2 R_A2 ->{A12}] R_A3.
rewrite mulmx_suml linear_sum summx_sub //= => i _.
by rewrite -mulmxA !mem_mulsmx.
Qed.

Lemma mulsmx_addl : forall m1 m2 m3 n (R1 : 'A_(m1, n)),
                    forall (R2 : 'A_(m2, n)) (R3 : 'A_(m3, n)),
  ((R1 + R2) * R3 = R1 * R3 + R2 * R3)%MS.
Proof.
move=> m1 m2 m3 n R1 R2 R3.
rewrite -(genmx_muls R2 R3) -(genmx_muls R1 R3) -genmx_muls -genmx_adds.
apply/genmxP; rewrite andbC addsmx_sub !mulsmxS ?addsmxSl ?addsmxSr //=.
apply/mulsmx_subP=> A12 A3; case/memmx_addsP=> A2 R_A1 R_A2 R_A3.
by rewrite -(subrK A2 A12) mulmx_addl linearD addmx_sub_adds ?mem_mulsmx.
Qed.

Lemma mulsmx_addr : forall m1 m2 m3 n (R1 : 'A_(m1, n)),
                    forall (R2 : 'A_(m2, n)) (R3 : 'A_(m3, n)),
  (R1 * (R2 + R3) = R1 * R2 + R1 * R3)%MS.
Proof.
move=> m1 m2 m3 n R1 R2 R3.
rewrite -(genmx_muls R1 R3) -(genmx_muls R1 R2) -genmx_muls -genmx_adds.
apply/genmxP; rewrite andbC addsmx_sub !mulsmxS ?addsmxSl ?addsmxSr //=.
apply/mulsmx_subP=> A1 A23 R_A1; case/memmx_addsP=> A3 R_A2 R_A3.
by rewrite -(subrK A3 A23) mulmx_addr linearD addmx_sub_adds ?mem_mulsmx.
Qed.

Lemma mulsmx0 : forall m1 m2 n (R1 : 'A_(m1, n)), (R1 * (0 : 'A_(m2, n)) = 0)%MS.
Proof.
move=> m1 m2 n R1; apply/eqP; rewrite -subsetmx0; apply/mulsmx_subP=> A1 A0 _.
by rewrite [A0 \in 0]eqmx0; move/memmx0->; rewrite mulmx0 mem0mx.
Qed.

Lemma muls0mx : forall m1 m2 n (R2 : 'A_(m2, n)), ((0 : 'A_(m1, n)) * R2 = 0)%MS.
Proof.
move=> m1 m2 n R1; apply/eqP; rewrite -subsetmx0; apply/mulsmx_subP=> A0 A2.
by rewrite [A0 \in 0]eqmx0; move/memmx0->; rewrite mul0mx mem0mx.
Qed.

Definition left_mx_ideal m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) :=
  (R1 * R2 <= R2)%MS.

Definition right_mx_ideal m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) :=
  (R2 * R1 <= R2)%MS.

Definition mx_ideal m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)) :=
  left_mx_ideal R1 R2 && right_mx_ideal R1 R2.

Definition mxring_id m n (R : 'M_(m, n ^2)) e :=
  [/\ e != 0,
      e \in R,
      forall A, A \in R -> e *m A = A
    & forall A, A \in R -> A *m e = A]%MS.

Definition has_mxring_id m n (R : 'M[F]_(m , n ^ 2)) :=
  (R != 0) &&
  (row_mx 0 (row_mx (mxvec R) (mxvec R))
    <= row_mx (cokermx R) (row_mx
         (lin1_mx (mxvec \o mulmx R \o lin_mulmx \o vec_mx))
         (lin1_mx (mxvec \o mulmx R \o lin_mulmxr \o vec_mx))))%MS.

Definition mxring m n (R : 'A_(m, n)) :=
  left_mx_ideal R R && has_mxring_id R.

Lemma mxring_idP : forall m n (R : 'A_(m, n)),
  reflect (exists e, mxring_id R e) (has_mxring_id R).
Proof.
move=> m n R; apply: (iffP andP) => [[nzR] | [e [nz_e Re ideR idRe]]].
  case/subsetmxP=> v; rewrite -[v]vec_mxK; move/vec_mx: v => e.
  rewrite !mul_mx_row; case/eq_row_mx; move/eqP.
  rewrite eq_sym -subsetmxE => Re.
  case/eq_row_mx; rewrite !{1}mul_rV_lin1 /= mxvecK.
  move/(can_inj mxvecK) => idRe; move/(can_inj mxvecK) => ideR.
  exists e; split=> // [|A|A].
  - by apply: contra nzR; rewrite ideR; move/eqP->; rewrite !linear0.
  - case/subsetmxP=> a defA; rewrite -{2}[A]mxvecK defA idRe.
    by rewrite mulmxA mx_rV_lin -defA /= mxvecK.
  case/subsetmxP=> a defA; rewrite -{2}[A]mxvecK defA ideR.
  by rewrite mulmxA mx_rV_lin -defA /= mxvecK.
split.
  apply: contra nz_e; move/eqP=> R0; rewrite R0 eqmx0 in Re.
  by rewrite (memmx0 Re).
apply/subsetmxP; exists (mxvec e); rewrite !mul_mx_row !{1}mul_rV_lin1.
rewrite subsetmxE in Re; rewrite {Re}(eqP Re).
congr (row_mx 0 (row_mx (mxvec _) (mxvec _))); apply/row_matrixP=> i.
  by rewrite !row_mul !mul_rV_lin1 /= mxvecK ideR vec_mxK ?row_sub.
by rewrite !row_mul !mul_rV_lin1 /= mxvecK idRe vec_mxK ?row_sub.
Qed.
Implicit Arguments mxring_idP [m n R].

Definition cent_mx_fun m n (R : 'A_(m, n)) (B : 'M[F]_n) :=
  R *m lin_mx (add_lin (mulmxr B) (-%R \o mulmx B)).

Lemma cent_mx_linear_proof : forall m n (R : 'A_(m, n)), linear (cent_mx_fun R).
Proof.
move=> m n R a A B; apply/row_matrixP=> i; rewrite linearP row_mul mul_rV_lin.
rewrite /= {-3}[row]lock row_mul mul_rV_lin -lock row_mul mul_rV_lin -linearP.
by rewrite -(linearP [linear of add_lin (mulmx _) (-%R \o mulmxr _)]).
Qed.
Canonical Structure cent_mx_linear m n (R : 'A_(m, n)) :=
  LinearFun (cent_mx_linear_proof R).

Definition cent_mx m n (R : 'A_(m, n)) := kermx (lin_mx (cent_mx_fun R)).
Local Notation "''C' ( R )" := (cent_mx R) : matrix_set_scope.

Definition center_mx m n (R : 'A_(m, n)) := (R :&: 'C(R))%MS.

Local Notation "''Z' ( R )" := (center_mx R) : matrix_set_scope.

Lemma cent_rowP : forall m n B (R : 'A_(m, n)),
  reflect (forall i (A := vec_mx (row i R)), A *m B = B *m A) (B \in 'C(R))%MS.
Proof.
move=> m n R B; apply: (iffP sub_kermxP); rewrite mul_vec_lin => cBE.
  move/(canRL mxvecK): cBE => cBE i A /=; move/(congr1 (row i)): cBE.
  rewrite row_mul mul_rV_lin -/A; move/(canRL mxvecK).
  by move/(canRL (subrK _)); rewrite !linear0 add0r.
apply: (canLR vec_mxK); apply/row_matrixP=> i.
by rewrite row_mul mul_rV_lin /= cBE subrr !linear0.
Qed.
Implicit Arguments cent_rowP [m n B R].

Lemma cent_mxP : forall m n B (R : 'A_(m, n)),
  reflect (forall A, A \in R -> A *m B = B *m A) (B \in 'C(R))%MS.
Proof.
move=> m n B R; apply: (iffP cent_rowP) => cEB => [A sAE | i A].
  rewrite -[A]mxvecK -(mulmxKpV sAE); move: (mxvec A *m _) => u.
  rewrite !mulmx_sum_row !linear_sum mulmx_suml; apply: eq_bigr => i _ /=.
  by rewrite !linearZ -scalemxAl /= cEB.
by rewrite cEB // vec_mxK row_sub.
Qed.
Implicit Arguments cent_mxP [m n B R].

Lemma scalar_mx_cent : forall m n a (R : 'A_(m, n)), (a%:M \in 'C(R))%MS.
Proof. by move=> m n a R; apply/cent_mxP=> A _; exact: scalar_mxC. Qed.

Lemma center_mx_sub : forall m n (R : 'A_(m, n)), ('Z(R) <= R)%MS.
Proof. move=> m n R; exact: capmxSl. Qed.

Lemma center_mxP : forall m n A (R : 'A_(m, n)),
  reflect (A \in R /\ forall B, B \in R -> B *m A = A *m B)
          (A \in 'Z(R))%MS.
Proof.
move=> m n A R; rewrite sub_capmx; case R_A: (A \in R); last by right; case.
by apply: (iffP cent_mxP) => [cAR | [_ cAR]].
Qed.
Implicit Arguments center_mxP [m n A R].

Lemma mxring_id_uniq : forall m n (R : 'A_(m, n)) e1 e2,
  mxring_id R e1 -> mxring_id R e2 -> e1 = e2.
Proof.
move=> m n R e1 e2 [_ Re1 idRe1 _] [_ Re2 _ ide2R].
by rewrite -(idRe1 _ Re2) ide2R.
Qed.

Lemma cent_mx_ideal : forall m n (R : 'A_(m, n)),
  left_mx_ideal 'C(R)%MS 'C(R)%MS.
Proof.
move=> m n R; apply/mulsmx_subP=> A1 A2 C_A1 C_A2; apply/cent_mxP=> B R_B.
by rewrite mulmxA (cent_mxP C_A1) // -!mulmxA (cent_mxP C_A2).
Qed.

Lemma cent_mx_ring : forall m n (R : 'A_(m, n)), n > 0 -> mxring 'C(R)%MS.
Proof.
move=> m n R n_gt0; rewrite /mxring cent_mx_ideal; apply/mxring_idP.
exists 1%:M; split=> [||A _|A _]; rewrite ?mulmx1 ?mul1mx ?scalar_mx_cent //.
by rewrite -mxrank_eq0 mxrank1 -lt0n.
Qed.

Lemma mxdirect_adds_center : forall m1 m2 n (R1 : 'A_(m1, n)) (R2 : 'A_(m2, n)),
    mx_ideal (R1 + R2)%MS R1 -> mx_ideal (R1 + R2)%MS R2 -> mxdirect (R1 + R2) ->
  ('Z((R1 + R2)%MS) :=: 'Z(R1) + 'Z(R2))%MS.
Proof.
move=> m1 m2 n R1 R2; case/andP=> idlR1 idrR1; case/andP=> idlR2 idrR2.
move/mxdirect_addsP=> dxR12.
apply/eqmxP; apply/andP; split.
  apply/memmx_subP=> z; rewrite sub_capmx; case/andP.
  case/memmx_addsP=> z2 R1z1 R2z2 Cz.
  rewrite -(subrK z2 z) linearD addmx_sub_adds //= ?sub_capmx ?R1z1 ?R2z2 /=.
    apply/cent_mxP=> A R1_A; have R_A := subsetmx_trans R1_A (addsmxSl R1 R2).
    have Rz2 := subsetmx_trans R2z2 (addsmxSr R1 R2).
    rewrite mulmx_subr (cent_mxP Cz) // mulmx_subl [A *m z2]memmx0.
      rewrite [z2 *m A]memmx0 //.
      by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
    by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
  apply/cent_mxP=> A R2_A; have R_A := subsetmx_trans R2_A (addsmxSr R1 R2).
  have Rz1 := subsetmx_trans R1z1 (addsmxSl R1 R2).
  rewrite -(subrK z z2) -oppr_sub addrC mulmx_subr (cent_mxP Cz) //.
  rewrite mulmx_subl [A *m _]memmx0 1?[(z - _) *m A]memmx0 //.
    by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
  by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
rewrite addsmx_sub; apply/andP; split.
  apply/memmx_subP=> z; rewrite sub_capmx; case/andP=> R1z cR1z.
  have Rz := subsetmx_trans R1z (addsmxSl R1 R2).
  rewrite sub_capmx Rz; apply/cent_mxP=> A; case/memmx_addsP=> A2 R1_A1 R2_A2.
  have R_A2 := subsetmx_trans R2_A2 (addsmxSr R1 R2).
  rewrite -(subrK A2 A) mulmx_addl (cent_mxP cR1z) // (mulmx_addr z _ A2).
  rewrite [A2 *m z]memmx0 1?[z *m A2]memmx0 //.
    by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
  by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
apply/memmx_subP=> z; rewrite !sub_capmx; case/andP=> R2z cR2z.
have Rz := subsetmx_trans R2z (addsmxSr R1 R2); rewrite Rz addsmxC.
apply/cent_mxP=> A; case/memmx_addsP=> A1 R2_A2 R1_A1.
have R_A1 := subsetmx_trans R1_A1 (addsmxSl R1 R2).
rewrite -(subrK A1 A) mulmx_addl (cent_mxP cR2z) // (mulmx_addr z _ A1).
rewrite [A1 *m z]memmx0 1?[z *m A1]memmx0 //.
  by rewrite -dxR12 sub_capmx (mulsmx_subP idlR1) // (mulsmx_subP idrR2).
by rewrite -dxR12 sub_capmx (mulsmx_subP idrR1) // (mulsmx_subP idlR2).
Qed.

Lemma mxdirect_sums_center : forall (I : finType) m n (R : 'A_(m, n)) R_,
    (\sum_i R_ i :=: R)%MS -> mxdirect (\sum_i R_ i) ->
    (forall i : I, mx_ideal R (R_ i)) ->
  ('Z(R) :=: \sum_i 'Z(R_ i))%MS.
Proof.
move=> I m n R R_ defR dxR idealR.
have sR_R: (R_ _ <= R)%MS by move=> i; rewrite -defR (sumsmx_sup i).
have anhR: forall i j A B, i != j -> A \in R_ i -> B \in R_ j -> A *m B = 0.
  move=> i j A B ne_ij RiA RjB; apply: memmx0.
  have [[_ idRiR] [idRRj _]] := (andP (idealR i), andP (idealR j)).
  rewrite -(mxdirect_sumsP dxR j) // sub_capmx (sumsmx_sup i) //.
    by rewrite (mulsmx_subP idRRj) // (memmx_subP (sR_R i)).
  by rewrite (mulsmx_subP idRiR) // (memmx_subP (sR_R j)).
apply/eqmxP; apply/andP; split.
  apply/memmx_subP=> Z; rewrite sub_capmx; case/andP.
  rewrite -{1}defR; case/memmx_sumsP=> z ->{Z} Rz cRz.
  apply/memmx_sumsP; exists z => // i; rewrite sub_capmx Rz.
  apply/cent_mxP=> A RiA; have:= cent_mxP cRz A (memmx_subP (sR_R i) A RiA).
  rewrite (bigD1 i) //= mulmx_addl mulmx_addr mulmx_suml mulmx_sumr.
  by rewrite !big1 ?addr0 // => j; last rewrite eq_sym; move/anhR->.
apply/sumsmx_subP => i _; apply/memmx_subP=> z; rewrite sub_capmx.
case/andP=> Riz cRiz; rewrite sub_capmx (memmx_subP (sR_R i)) //=.
apply/cent_mxP=> A; rewrite -{1}defR; case/memmx_sumsP=> a -> R_a.
rewrite (bigD1 i) // mulmx_addl mulmx_addr mulmx_suml mulmx_sumr.
rewrite !big1 => [|j|j]; first by rewrite !addr0 (cent_mxP cRiz).
  by rewrite eq_sym; move/anhR->.
by move/anhR->.
Qed.

End MatrixAlgebra.

Arguments Scope mulsmx
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope left_mx_ideal
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope right_mx_ideal
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope mx_ideal
  [_ nat_scope nat_scope nat_scope matrix_set_scope matrix_set_scope].
Arguments Scope mxring_id
  [_ nat_scope nat_scope ring_scope matrix_set_scope].
Arguments Scope has_mxring_id
  [_ nat_scope nat_scope ring_scope matrix_set_scope].
Arguments Scope mxring
  [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope cent_mx
  [_ nat_scope nat_scope matrix_set_scope].
Arguments Scope center_mx
  [_ nat_scope nat_scope matrix_set_scope].

Prenex Implicits mulsmx.

Notation "A \in R" := (subsetmx (mxvec A) R) : matrix_set_scope.
Notation "R * S" := (mulsmx R S) : matrix_set_scope.
Notation "''C' ( R )" := (cent_mx R) : matrix_set_scope.
Notation "''C_' R ( S )" := (R :&: 'C(S))%MS : matrix_set_scope.
Notation "''Z' ( R )" := (center_mx R) : matrix_set_scope.

Implicit Arguments memmx_subP [F m1 m2 n R1 R2].
Implicit Arguments memmx_eqP [F m1 m2 n R1 R2].
Implicit Arguments memmx_addsP [F m1 m2 n R1 R2].
Implicit Arguments memmx_sumsP [F I P n A R_].
Implicit Arguments mulsmx_subP [F m1 m2 m n R1 R2 R].
Implicit Arguments mulsmxP [F m1 m2 n A R1 R2].
Implicit Arguments mxring_idP [m n R].
Implicit Arguments cent_rowP [F m n B R].
Implicit Arguments cent_mxP [F m n B R].
Implicit Arguments center_mxP [F m n A R].

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

Definition powers_mx d := \matrix_(i < d) mxvec (A ^+ i).

Lemma horner_rVpoly : forall m (u : 'rV_m),
  horner_mx (rVpoly u) = vec_mx (u *m powers_mx m).
Proof.
move=> m u; rewrite mulmx_sum_row linear_sum [rVpoly u]poly_def ringM_sum //.
by apply: eq_bigr => i _; rewrite valK horner_mx_CXn linearZ rowK /= mxvecK.
Qed.

Fact degree_mxminpoly_proof : exists d, \rank (powers_mx d.+1) <= d.
Proof. by exists (n ^ 2)%N; rewrite rank_leq_col. Qed.
Definition degree_mxminpoly := ex_minn degree_mxminpoly_proof.
Local Notation d := degree_mxminpoly.
Local Notation Ad := (powers_mx d).

Lemma mxminpoly_nonconstant : d > 0.
Proof.
rewrite /d; case: ex_minnP; case=> //; rewrite leqn0 mxrank_eq0; move/eqP.
move/row_matrixP; move/(_ 0); move/eqP; rewrite rowK row0 mxvec_eq0.
by rewrite -mxrank_eq0 mxrank1.
Qed.

Lemma minpoly_mx1 : (1%:M \in Ad)%MS.
Proof.
by apply: (eq_row_sub (Ordinal mxminpoly_nonconstant)); rewrite rowK.
Qed.

Lemma minpoly_mx_free : row_free Ad.
Proof.
have:= mxminpoly_nonconstant; rewrite /d; case: ex_minnP; case=> // d' _.
move/(_ d'); move/implyP; rewrite ltnn implybF -ltnS ltn_neqAle.
by rewrite rank_leq_row andbT negbK.
Qed.

Lemma horner_mx_mem : forall p, (horner_mx p \in Ad)%MS.
Proof.
apply:poly_ind=> [|p a IHp]; first by rewrite ringM_0 // linear0 subset0mx.
rewrite ringM_add // ringM_mul // horner_mx_C horner_mx_X.
rewrite addrC -scalemx1 linearP /= -(mul_vec_lin (mulmxr_linear _ A)).
case/subsetmxP: IHp => u ->{i}.
have: (powers_mx (1 + d) <= Ad)%MS.
  rewrite -(geq_leqif (mxrank_leqif_sup _)).
    by rewrite (eqnP minpoly_mx_free) /d; case: ex_minnP.
  rewrite addnC; apply/row_subP=> {i}i.
  by apply: eq_row_sub (lshift 1 i) _; rewrite !rowK.
apply: subsetmx_trans; rewrite addmx_sub ?scalemx_sub //.
  by apply: (eq_row_sub 0); rewrite rowK.
rewrite -mulmxA mulmx_sub {u}//; apply/row_subP=> i.
rewrite row_mul rowK mul_vec_lin /= mulmxE -exprSr.
by apply: (eq_row_sub (rshift 1 i)); rewrite rowK.
Qed.

Definition mx_inv_horner B := rVpoly (mxvec B *m pinvmx Ad).

Lemma mx_inv_horner0 :  mx_inv_horner 0 = 0.
Proof. by rewrite /mx_inv_horner linear0 mul0mx rVpoly0. Qed.

Lemma mx_inv_hornerK : forall B,
  (B \in Ad)%MS -> horner_mx (mx_inv_horner B) = B.
Proof. by move=> B sBAd; rewrite horner_rVpoly mulmxKpV ?mxvecK. Qed.

Lemma minpoly_mxM : forall B C, (B \in Ad -> C \in Ad -> B * C \in Ad)%MS.
Proof.
move=> B C AdB AdC; rewrite -(mx_inv_hornerK AdB) -(mx_inv_hornerK AdC).
by rewrite -ringM_mul ?horner_mx_mem.
Qed.

Lemma minpoly_mx_ring : mxring Ad.
Proof.
apply/andP; split; first by apply/mulsmx_subP; exact: minpoly_mxM.
apply/mxring_idP; exists 1%:M; split=> *; rewrite ?mulmx1 ?mul1mx //.
  by rewrite -mxrank_eq0 mxrank1.
exact: minpoly_mx1.
Qed.

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
by rewrite ringM_sub // -horner_mx_Xn mx_inv_hornerK ?subrr ?horner_mx_mem.
Qed.

Lemma horner_rVpolyK : forall u : 'rV_d,
  mx_inv_horner (horner_mx (rVpoly u)) = rVpoly u.
Proof.
move=> u; congr rVpoly; rewrite horner_rVpoly vec_mxK.
by apply: (row_free_inj minpoly_mx_free); rewrite mulmxKpV ?subsetmxMl.
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
have scalP := has_non_scalar_mxP minpoly_mx1.
rewrite leqNgt -(eqnP minpoly_mx_free); apply/scalP/idP=> [|[[B]]].
  case scalA: (is_scalar_mx A); [by right | left].
  by exists A; rewrite ?scalA // -horner_mx_X horner_mx_mem.
move/mx_inv_hornerK=> <- nsB; case/is_scalar_mxP=> a defA; case/negP: nsB.
move:{B}(_ B); apply:poly_ind=> [|p c]; first by rewrite ringM_0 ?mx0_is_scalar.
rewrite ringM_add ?ringM_mul // horner_mx_X defA; case/is_scalar_mxP=> b ->.
by rewrite -(ringM_mul zRM) horner_mx_C -scalar_mx_add scalar_mx_is_scalar.
Qed.

End MinPoly.

Section GenRepr.

Variable F : fieldType.

Section OneRepresentation.

Variable gT : finGroupType.

Definition mx_repr (G : {set gT}) n (r : gT -> 'M[F]_n) :=
  r 1%g = 1%:M /\ {in G &, {morph r : x y / (x * y)%g >-> x *m y}}.

Structure mx_representation G n :=
  MxRepresentation { repr_mx :> gT -> 'M_n; _ : mx_repr G repr_mx }.

Variables (G : {group gT}) (n : nat) (rG : mx_representation G n).
Arguments Scope rG [group_scope].

Lemma repr_mx1 : rG 1 = 1%:M.
Proof. by case: rG => r []. Qed.

Lemma repr_mxM : {in G &, {morph rG : x y / (x * y)%g >-> x *m y}}.
Proof. by case: rG => r []. Qed.

Lemma repr_mxK : forall m x,
  x \in G ->  cancel ((@mulmx _ m n n)^~ (rG x)) (mulmx^~ (rG x^-1)).
Proof.
by move=> m x Gx U; rewrite -mulmxA -repr_mxM ?groupV // mulgV repr_mx1 mulmx1.
Qed.

Lemma repr_mxKV : forall m x,
  x \in G -> cancel ((@mulmx _ m n n)^~ (rG x^-1)) (mulmx^~ (rG x)).
Proof. move=> m x; rewrite -groupV -{3}[x]invgK; exact: repr_mxK. Qed.

Lemma repr_mx_unit : forall x, x \in G -> rG x \in unitmx.
Proof. by move=> x Gx; case/mulmx1_unit: (repr_mxKV Gx 1%:M). Qed.

Lemma repr_mx_free : forall x, x \in G -> row_free (rG x).
Proof. by move=> x Gx; rewrite row_free_unit repr_mx_unit. Qed.

Lemma repr_mxV : {in G, {morph rG : x / x^-1%g >-> invmx x}}.
Proof.
by move=> x Gx /=; rewrite -[rG x^-1](mulKmx (repr_mx_unit Gx)) mulmxA repr_mxK.
Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Definition rstab := [set x \in G | U *m rG x == U].
Definition rstabs := [set x \in G | U *m rG x <= U]%MS.

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
  x \in rstab -> (W <= U)%MS -> W *m rG x = W.
Proof.
move=> x m1 W; case/setIdP=> _; move/eqP=> cUx.
by case/subsetmxP=> w ->; rewrite -mulmxA cUx.
Qed.

Lemma rstabs_act : forall x m1 (W : 'M_(m1, n)),
  x \in rstabs -> (W <= U)%MS -> (W *m rG x <= U)%MS.
Proof.
move=> x m1 W; case/setIdP=> _ nUx sWU; apply: subsetmx_trans nUx.
exact: subsetmxMr.
Qed.

Definition mxmodule := G \subset rstabs.

Lemma mxmoduleP : reflect {in G, forall x, U *m rG x <= U}%MS mxmodule.
Proof.
by apply: (iffP subsetP) => modU x Gx; have:= modU x Gx; rewrite !inE ?Gx.
Qed.

End Stabilisers.
Implicit Arguments mxmoduleP [m U].

Lemma rstabS : forall m1 m2 U V, (U <= V)%MS -> @rstab m2 V \subset @rstab m1 U.
Proof.
move=> m1 m2 U V; case/subsetmxP=> u ->; apply/subsetP=> x; rewrite !inE.
by case/andP=> -> /= cVx; rewrite -mulmxA (eqP cVx).
Qed.

Lemma eqmx_rstab : forall m1 m2 U V, (U :=: V)%MS -> @rstab m1 U = @rstab m2 V.
Proof.
by move=> m1 m2 U V eqUV; apply/eqP; rewrite eqEsubset !rstabS ?eqUV.
Qed.

Lemma eqmx_rstabs : forall m1 m2 U V,
  (U :=: V)%MS -> @rstabs m1 U = @rstabs m2 V.
Proof.
by move=> m1 m2 U V eqUV; apply/setP=> x; rewrite !inE eqUV (eqmxMr _ eqUV).
Qed.

Lemma eqmx_module : forall m1 m2 U V,
  (U :=: V)%MS -> @mxmodule m1 U = @mxmodule m2 V.
Proof. by move=> m1 m2 U V eqUV; rewrite /mxmodule (eqmx_rstabs eqUV). Qed.

Lemma mxmodule0 : forall m, mxmodule (0 : 'M_(m, n)).
Proof. by move=> m; apply/mxmoduleP=> x _; rewrite mul0mx. Qed.

Lemma mxmodule1 : mxmodule 1%:M.
Proof. by apply/mxmoduleP=> x _; rewrite subsetmx1. Qed.

Lemma mxmodule_trans : forall m1 m2 (U : 'M_(m1, n)) (W : 'M_(m2, n)) x,
  mxmodule U -> x \in G -> (W <= U -> W *m rG x <= U)%MS.
Proof.
move=> m1 m2 U W x modU Gx sWU.
by apply: subsetmx_trans (mxmoduleP modU x Gx); exact: subsetmxMr.
Qed.

Lemma addsmx_module : forall m1 m2 U V,
  @mxmodule m1 U -> @mxmodule m2 V -> mxmodule (U + V)%MS.
Proof.
move=> m1 m2 U V modU modV; apply/mxmoduleP=> x Gx.
by rewrite addsmxMr addsmxS ?(mxmoduleP _ x Gx).
Qed.

Lemma sumsmx_module : forall I r (P : pred I) U,
  (forall i, P i -> mxmodule (U i)) -> mxmodule (\sum_(i <- r | P i) U i)%MS.
Proof.
move=> I r P U modU.
by apply big_prop; [exact: mxmodule0 | exact: addsmx_module | exact: modU].
Qed.

Lemma capmx_module : forall m1 m2 U V,
  @mxmodule m1 U -> @mxmodule m2 V -> mxmodule (U :&: V)%MS.
Proof.
move=> m1 m2 U V modU modV; apply/mxmoduleP=> x Gx.
by rewrite sub_capmx !mxmodule_trans ?capmxSl ?capmxSr.
Qed.

Lemma bigcapmx_module : forall I r (P : pred I) U,
  (forall i, P i -> mxmodule (U i)) -> mxmodule (\bigcap_(i <- r | P i) U i)%MS.
Proof.
move=> I r P U modU.
by apply big_prop; [exact: mxmodule1 | exact: capmx_module | exact: modU].
Qed.

(* Sub- and factor representations induced by a (sub)module. *)
Section Submodule.

Variable U : 'M[F]_n.

Definition val_submod m : 'M_(m, \rank U) -> 'M_(m, n) := mulmxr (row_base U).
Definition in_submod m : 'M_(m, n) -> 'M_(m, \rank U) :=
   mulmxr (invmx (row_ebase U) *m pid_mx (\rank U)).
Canonical Structure val_submod_linear m := [linear of @val_submod m].
Canonical Structure in_submod_linear m := [linear of @in_submod m].

Lemma val_submodE : forall m W, @val_submod m W = W *m val_submod 1%:M.
Proof. by move=> w M; rewrite mulmxA mulmx1. Qed.

Lemma in_submodE : forall m W, @in_submod m W = W *m in_submod 1%:M.
Proof. by move=> w M; rewrite mulmxA mulmx1. Qed.

Lemma val_submod1 : (val_submod 1%:M :=: U)%MS.
Proof. by rewrite /val_submod /= mul1mx; exact: eq_row_base. Qed.

Lemma val_submodP : forall m W, (@val_submod m W <= U)%MS.
Proof. by move=> m W; rewrite mulmx_sub ?eq_row_base. Qed.

Lemma val_submodK : forall m, cancel (@val_submod m) (@in_submod m).
Proof.
move=> w W; rewrite /in_submod /= -!mulmxA mulKVmx ?row_ebase_unit //.
by rewrite pid_mx_id ?rank_leq_row // pid_mx_1 mulmx1.
Qed.

Lemma val_submod_inj : forall m, injective (@val_submod m).
Proof. move=> m; exact: can_inj (@val_submodK m). Qed.

Lemma val_submodS : forall m1 m2 (V : 'M_(m1, \rank U)) (W : 'M_(m2, \rank U)),
  (val_submod V <= val_submod W)%MS = (V <= W)%MS.
Proof.
move=> m1 m2 V W; apply/idP/idP=> sVW; last exact: subsetmxMr.
by rewrite -[V]val_submodK -[W]val_submodK subsetmxMr.
Qed.

Lemma in_submodK : forall m W, (W <= U)%MS -> val_submod (@in_submod m W) = W.
Proof.
move=> m W; case/subsetmxP=> w ->; rewrite /val_submod /= -!mulmxA.
congr (_ *m _); rewrite -{1}[U]mulmx_ebase !mulmxA mulmxK ?row_ebase_unit //.
by rewrite -2!(mulmxA (col_ebase U)) !pid_mx_id ?rank_leq_row // mulmx_ebase.
Qed.

Lemma val_submod_eq0 : forall m W, (@val_submod m W == 0) = (W == 0).
Proof.
by move=> m W; rewrite -!subsetmx0 -val_submodS linear0 !(subsetmx0, eqmx0).
Qed.

Lemma in_submod_eq0 : forall m W, (@in_submod m W == 0) = (W <= U^C)%MS.
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

Lemma val_factmodE : forall m W, @val_factmod m W = W *m val_factmod 1%:M.
Proof. by move=> w M; rewrite mulmxA mulmx1. Qed.

Lemma in_factmodE : forall m W, @in_factmod m W = W *m in_factmod 1%:M.
Proof. by move=> w M; rewrite mulmxA mulmx1. Qed.

Lemma val_factmodP : forall m W, (@val_factmod m W <= U^C)%MS.
Proof.
move=> m W; rewrite mulmx_sub {m W}// (eqmxMr _ (eq_row_base _)).
by rewrite -mulmxA subsetmxMl.
Qed.

Lemma val_factmodK : forall m, cancel (@val_factmod m) (@in_factmod m).
Proof.
move=> m W /=; rewrite /in_factmod /=; set Uc := cokermx U.
apply: (row_free_inj (row_base_free Uc)); rewrite -mulmxA mulmx_base.
rewrite /val_factmod /= 2!mulmxA -/Uc mulmxK ?row_ebase_unit //.
have: (row_base Uc <= Uc)%MS by rewrite eq_row_base.
by case/subsetmxP=> u ->; rewrite -!mulmxA copid_mx_id ?rank_leq_row.
Qed.

Lemma val_factmod_inj : forall m, injective (@val_factmod m).
Proof. move=> m; exact: can_inj (@val_factmodK m). Qed.

Lemma val_factmodS : forall m1 m2 (V : 'M_(m1, _)) (W : 'M_(m2, _)),
  (val_factmod V <= val_factmod W)%MS = (V <= W)%MS.
Proof.
move=> m1 m2 V W; apply/idP/idP=> sVW; last exact: subsetmxMr.
by rewrite -[V]val_factmodK -[W]val_factmodK subsetmxMr.
Qed.

Lemma val_factmod_eq0 : forall m W, (@val_factmod m W == 0) = (W == 0).
Proof.
by move=> m W; rewrite -!subsetmx0 -val_factmodS linear0 !(subsetmx0, eqmx0).
Qed.

Lemma in_factmod_eq0 : forall m (W : 'M_(m, n)),
  (in_factmod W == 0) = (W <= U)%MS.
Proof.
move=> m W; rewrite subsetmxE -!mxrank_eq0 -{2}[_ U]mulmx_base mulmxA.
by rewrite (mxrankMfree _ (row_base_free _)).
Qed.

Lemma in_factmodK : forall m (W : 'M_(m, n)),
  (W <= U^C)%MS -> val_factmod (in_factmod W) = W.
Proof.
move=> m W; case/subsetmxP=> w ->{W}; rewrite /val_factmod /= -2!mulmxA.
congr (_ *m _); rewrite (mulmxA (col_base _)) mulmx_base -2!mulmxA.
by rewrite mulKVmx ?row_ebase_unit // mulmxA copid_mx_id ?rank_leq_row.
Qed.

Lemma in_factmod_addsK : forall m (W : 'M_(m, n)),
  (in_factmod (U + W)%MS :=: in_factmod W)%MS.
Proof.
move=> m W; apply: eqmx_trans (addsmxMr _ _ _) _.
rewrite ((_ *m _ =P 0) _) ?in_factmod_eq0 //; exact: adds0mx.
Qed.

Lemma add_sub_fact_mod : forall m (W : 'M_(m, n)),
  val_submod (in_submod W) + val_factmod (in_factmod W) = W.
Proof.
move=> m W; rewrite /val_submod /val_factmod /= -!mulmxA -mulmx_addr.
rewrite addrC (mulmxA (pid_mx _)) pid_mx_id // (mulmxA (col_ebase _)).
rewrite (mulmxA _ _ (row_ebase _)) mulmx_ebase.
rewrite (mulmxA (pid_mx _)) pid_mx_id // mulmxA -mulmx_addl -mulmx_addr.
by rewrite subrK mulmx1 mulmxA mulmxKV ?row_ebase_unit.
Qed.

Lemma proj_factmodS : forall m (W : 'M_(m, n)),
  (val_factmod (in_factmod W) <= U + W)%MS.
Proof.
move=> m W.
by rewrite -{2}[W]add_sub_fact_mod addsmx_addKl ?val_submodP ?addsmxSr.
Qed.

Lemma in_factmodsK : forall m (W : 'M_(m, n)),
  (U <= W)%MS -> (U + val_factmod (in_factmod W) :=: W)%MS.
Proof.
move=> m W; move/addsmx_idPr; apply: eqmx_trans (eqmx_sym _).
by rewrite -{1}[W]add_sub_fact_mod; apply: addsmx_addKl; exact: val_submodP.
Qed.

Lemma mxrank_in_factmod : forall m (W : 'M_(m, n)),
  (\rank (in_factmod W) + \rank U)%N = \rank (U + W).
Proof.
move=> m W; rewrite -in_factmod_addsK in_factmodE; set fU := in_factmod 1%:M.
suffices <-: ((U + W) :&: kermx fU :=: U)%MS by rewrite mxrank_mul_ker.
apply: eqmx_trans (capmx_idPr (addsmxSl U W)).
apply: cap_eqmx => //; apply/eqmxP; apply/rV_eqP => u.
by rewrite (sameP sub_kermxP eqP) -in_factmodE in_factmod_eq0.
Qed.

Definition submod_mx of mxmodule U :=
  fun x => in_submod (val_submod 1%:M *m rG x).

Definition factmod_mx of mxmodule U :=
  fun x => in_factmod (val_factmod 1%:M *m rG x).

Hypothesis Umod : mxmodule U.

Lemma in_submodJ : forall m (W : 'M_(m, n)) x,
  (W <= U)%MS -> in_submod (W *m rG x) = in_submod W *m submod_mx Umod x.
Proof.
move=> m W x sWU; rewrite mulmxA; congr (in_submod _).
by rewrite mulmxA -val_submodE in_submodK.
Qed.

Lemma val_submodJ : forall m (W : 'M_(m, \rank U)) x,
  x \in G -> val_submod (W *m submod_mx Umod x) = val_submod W *m rG x.
Proof.
move=> m W x Gx; rewrite 2!(mulmxA W) -val_submodE in_submodK //.
by rewrite mxmodule_trans ?val_submodP.
Qed.

Lemma submod_mx_repr : mx_repr G (submod_mx Umod).
Proof.
rewrite /submod_mx; split=> [|x y Gx Gy /=].
  by rewrite repr_mx1 mulmx1 val_submodK.
rewrite -in_submodJ; first by rewrite repr_mxM ?mulmxA.
by rewrite mxmodule_trans ?val_submodP.
Qed.

Canonical Structure submod_repr := MxRepresentation submod_mx_repr.

Lemma in_factmodJ : forall m (W : 'M_(m, n)) x,
  x \in G -> in_factmod (W *m rG x) = in_factmod W *m factmod_mx Umod x.
Proof.
move=> m W x Gx; rewrite -{1}[W]add_sub_fact_mod mulmx_addl linearD /=.
apply: (canLR (subrK _)); apply: etrans (_ : 0 = _).
  apply/eqP; rewrite in_factmod_eq0 (subsetmx_trans _ (mxmoduleP Umod x Gx)) //.
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

End Submodule.

(* The enveloping algebra, represented as a subspace of 'rV_(n ^ 2). *)

Definition enveloping_algebra_mx := \matrix_(i < #|G|) mxvec (rG (enum_val i)).
Local Notation E_G := enveloping_algebra_mx.

Lemma envelop_mx_id : forall x, x \in G -> (rG x \in E_G)%MS.
Proof.
by move=> x Gx; rewrite (eq_row_sub (enum_rank_in Gx x)) // rowK enum_rankK_in.
Qed.

Lemma envelop_mx1 : (1%:M \in E_G)%MS.
Proof. by rewrite -repr_mx1 envelop_mx_id. Qed.

Lemma envelop_mxP : forall A,
  reflect (exists a, A = \sum_(x \in G) a x *m: rG x) (A \in E_G)%MS.
Proof.
have G_1 := group1 G; have bijG := enum_val_bij_in G_1.
set h := enum_val in bijG; have Gh: h _ \in G by exact: enum_valP.
move=> A; apply: (iffP subsetmxP) => [[u defA] | [a ->]].
  exists (fun x => u 0 (enum_rank_in G_1 x)); apply: (can_inj mxvecK).
  rewrite defA mulmx_sum_row linear_sum (reindex h) //=.
  by apply: eq_big => [i | i _]; rewrite ?Gh // rowK linearZ enum_valK_in.
exists (\row_i a (h i)); rewrite mulmx_sum_row linear_sum (reindex h) //=.
by apply: eq_big => [i | i _]; rewrite ?Gh // mxE rowK linearZ.
Qed.

Lemma envelop_mxM : forall A B, (A \in E_G -> B \in E_G -> A *m B \in E_G)%MS.
Proof.
move=> A B; case/envelop_mxP=> a ->{A}; case/envelop_mxP=> b ->{B}.
rewrite mulmx_suml !linear_sum summx_sub //= => x Gx.
rewrite !linear_sum summx_sub //= => y Gy.
rewrite -scalemxAl !(linearZ, scalemx_sub) //= -repr_mxM //.
by rewrite envelop_mx_id ?groupM.
Qed.

Lemma mxmodule_envelop : forall m1 m2 (U : 'M_(m1, n)) (W : 'M_(m2, n)) A,
  (mxmodule U -> mxvec A <= E_G -> W <= U -> W *m A <= U)%MS.
Proof.
move=> m1 m2 U W A modU; case/envelop_mxP=> a -> sWU.
rewrite linear_sum summx_sub // => x Gx.
by rewrite linearZ scalemx_sub ?mxmodule_trans.
Qed.

(* Module homomorphisms; any square matrix f defines a module homomorphism   *)
(* over some domain, namely, dom_hom_mx f.                                   *)

Definition dom_hom_mx f : 'M_n :=
  kermx (lin1_mx (mxvec \o mulmx (cent_mx_fun E_G f) \o lin_mul_row)).

Lemma hom_mxP : forall m f (W : 'M_(m, n)),
  reflect (forall x, x \in G -> W *m rG x *m f = W *m f *m rG x)
          (W <= dom_hom_mx f)%MS.
Proof.
move=> m f W; apply: (iffP row_subP) => [cGf x Gx | cGf i].
  apply/row_matrixP=> i; apply/eqP; rewrite -subr_eq0 -!mulmxA -!linear_sub /=.
  have:= sub_kermxP (cGf i); rewrite mul_rV_lin1 /=; move/(canRL mxvecK).
  move/row_matrixP; move/(_ (enum_rank_in Gx x)); move/eqP; rewrite !linear0.
  by rewrite !row_mul rowK mul_vec_lin /= mul_vec_lin_row enum_rankK_in.
apply/sub_kermxP; rewrite mul_rV_lin1 /=; apply: (canLR vec_mxK).
apply/row_matrixP=> j; rewrite !row_mul rowK mul_vec_lin /= mul_vec_lin_row.
by rewrite -!row_mul mulmx_subr !mulmxA cGf ?enum_valP // subrr !linear0.
Qed.
Implicit Arguments hom_mxP [m f W].

Lemma hom_envelop_mxC : forall m f (W : 'M_(m, n)) A,
  (W <= dom_hom_mx f -> A \in E_G -> W *m A *m f = W *m f *m A)%MS.
Proof.
move=> m f W A; move/hom_mxP=> cWfG; case/envelop_mxP=> a ->.
rewrite !linear_sum mulmx_suml; apply: eq_bigr => x Gx.
by rewrite !linearZ -scalemxAl /= cWfG.
Qed.

Lemma dom_hom_invmx : forall f,
  f \in unitmx -> (dom_hom_mx (invmx f) :=: dom_hom_mx f *m f)%MS.
Proof.
move=> f injf; set U := dom_hom_mx _; apply/eqmxP.
rewrite -{1}[U](mulmxKV injf) subsetmxMr; apply/hom_mxP=> x Gx.
  by rewrite -[_ *m rG x](hom_mxP _) ?mulmxK.
by rewrite -[_ *m rG x](hom_mxP _) ?mulmxKV.
Qed.

Lemma dom_hom_mx_module : forall f, mxmodule (dom_hom_mx f).
Proof.
move=> f; apply/mxmoduleP=> x Gx; apply/hom_mxP=> y Gy.
rewrite -[_ *m rG y]mulmxA -repr_mxM // 2?(hom_mxP _) ?groupM //.
by rewrite repr_mxM ?mulmxA.
Qed.

Lemma hom_mxmodule : forall m (U : 'M_(m, n)) f,
  (U <= dom_hom_mx f)%MS -> mxmodule U -> mxmodule (U *m f).
Proof.
move=> m U f; move/hom_mxP=> cGfU modU; apply/mxmoduleP=> x Gx.
by rewrite -cGfU // subsetmxMr // (mxmoduleP modU).
Qed.

Lemma kermx_hom_module : forall m (U : 'M_(m, n)) f,
  (U <= dom_hom_mx f)%MS -> mxmodule U -> mxmodule (U :&: kermx f)%MS.
Proof.
move=> m U f homUf modU; apply/mxmoduleP=> x Gx.
rewrite sub_capmx mxmodule_trans ?capmxSl //=.
apply/sub_kermxP; rewrite (hom_mxP _) ?(subsetmx_trans (capmxSl _ _)) //.
by rewrite (sub_kermxP (capmxSr _ _)) mul0mx.
Qed.

Lemma scalar_mx_hom : forall a m (U : 'M_(m, n)), (U <= dom_hom_mx a%:M)%MS.
Proof. by move=> a m U; apply/hom_mxP=> x Gx; rewrite -!mulmxA scalar_mxC. Qed.

Lemma proj_mx_hom : forall U V : 'M_n,
    (U :&: V = 0)%MS -> mxmodule U -> mxmodule V ->
  (U + V <= dom_hom_mx (proj_mx U V))%MS.
Proof.
move=> U V dxUV modU modV; apply/hom_mxP=> x Gx.
rewrite -{1}(add_proj_mx dxUV (subsetmx_refl _)) !mulmx_addl addrC.
rewrite {1}[_ *m _]proj_mx_0 ?add0r //; last first.
  by rewrite mxmodule_trans ?proj_mx_sub.
by rewrite [_ *m _](proj_mx_id dxUV) // mxmodule_trans ?proj_mx_sub.
Qed.

(* The subspace fixed by a subgroup H of G; it is a module if H <| G.         *)
(* The definition below is extensionally equivalent to the straightforward    *)
(*    \bigcap_(x \in H) kermx (rG x - 1%:M)                                   *)
(* but it avoids the dependency on the choice function; this allows it to     *)
(* commute with ring morphisms.                                               *)

Definition rfix_mx (H : {set gT}) :=
  let commrH := \matrix_(i < #|H|) mxvec (rG (enum_val i) - 1%:M) in
  kermx (lin1_mx (mxvec \o mulmx commrH \o lin_mul_row)).

Lemma rfix_mxP : forall m (W : 'M_(m, n)) (H : {set gT}),
  reflect (forall x, x \in H -> W *m rG x = W) (W <= rfix_mx H)%MS.
Proof.
rewrite /rfix_mx => m W H; set C := \matrix_i _.
apply: (iffP row_subP) => [cHW x Hx | cHW j].
  apply/row_matrixP=> j; apply/eqP; rewrite -subr_eq0 row_mul.
  move/sub_kermxP: {cHW}(cHW j); rewrite mul_rV_lin1 /=; move/(canRL mxvecK).
  move/row_matrixP; move/(_ (enum_rank_in Hx x)); rewrite row_mul rowK !linear0.
  by rewrite enum_rankK_in // mul_vec_lin_row mulmx_subr mulmx1 => ->.
apply/sub_kermxP; rewrite mul_rV_lin1 /=; apply: (canLR vec_mxK).
apply/row_matrixP=> i; rewrite row_mul rowK mul_vec_lin_row -row_mul.
by rewrite mulmx_subr mulmx1 cHW ?enum_valP // subrr !linear0.
Qed.
Implicit Arguments rfix_mxP [m W].

Lemma normal_rfix_mx_module : forall H, H <| G -> mxmodule (rfix_mx H).
Proof.
move=> H; case/andP=> sHG nHG; apply/mxmoduleP=> x Gx.
apply/rfix_mxP=> y Hy; have Gy := subsetP sHG y Hy.
have Hyx: (y ^ x^-1)%g \in H by rewrite -mem_conjg (normsP nHG).
rewrite -mulmxA -repr_mxM // conjgCV repr_mxM ?(subsetP sHG _ Hyx) // mulmxA.
by rewrite (rfix_mxP H _ _ Hyx).
Qed.

Lemma rfix_mx_module : mxmodule (rfix_mx G).
Proof. exact: normal_rfix_mx_module. Qed.

Lemma rfix_mxS : forall H K : {set gT},
  H \subset K -> (rfix_mx K <= rfix_mx H)%MS.
Proof.
by move=> H K sHK; apply/rfix_mxP=> x Hx; exact: rfix_mxP (subsetP sHK x Hx).
Qed.

(* The cyclic module generated by a single vector. *)
Definition cyclic_mx u := <<E_G *m lin_mul_row u>>%MS.

Lemma cyclic_mxP : forall u v,
  reflect (exists2 A, A \in E_G & v = u *m A)%MS (v <= cyclic_mx u)%MS.
Proof.
move=> u v; rewrite genmxE; apply: (iffP subsetmxP) => [[a] | [A E_A]] -> {v}.
  exists (vec_mx (a *m E_G)); last by rewrite mulmxA mul_rV_lin1.
  by rewrite vec_mxK subsetmxMl.
case/subsetmxP: E_A => a defA.
by exists a; rewrite mulmxA mul_rV_lin1 /= -defA mxvecK.
Qed.
Implicit Arguments cyclic_mxP [u v].

Lemma cyclic_mx_id : forall u, (u <= cyclic_mx u)%MS.
Proof.
by move=> u; apply/cyclic_mxP; exists 1%:M; rewrite ?mulmx1 ?envelop_mx1.
Qed.

Lemma cyclic_mx_eq0 : forall u, (cyclic_mx u == 0) = (u == 0).
Proof.
move=> u; rewrite -!subsetmx0; apply/idP/idP.
  by apply: subsetmx_trans; exact: cyclic_mx_id.
move/subsetmx0null->; rewrite genmxE; apply/row_subP=> i.
by rewrite row_mul mul_rV_lin1 /= mul0mx ?subset0mx.
Qed.

Lemma cyclic_mx_module : forall u, mxmodule (cyclic_mx u).
Proof.
move=> u; apply/mxmoduleP=> x Gx; apply/row_subP=> i; rewrite row_mul.
have [A E_A ->{i}] := @cyclic_mxP u _ (row_sub i _); rewrite -mulmxA.
by apply/cyclic_mxP; exists (A *m rG x); rewrite ?envelop_mxM ?envelop_mx_id.
Qed.

Lemma cyclic_mx_sub : forall m u (W : 'M_(m, n)),
  mxmodule W -> (u <= W)%MS -> (cyclic_mx u <= W)%MS.
Proof.
move=> m u W modU Wu; rewrite genmxE; apply/row_subP=> i.
by rewrite row_mul mul_rV_lin1 /= mxmodule_envelop // vec_mxK row_sub.
Qed. 

Lemma hom_cyclic_mx : forall u f,
  (u <= dom_hom_mx f)%MS -> (cyclic_mx u *m f :=: cyclic_mx (u *m f))%MS.
Proof.
move=> u f domf_u; apply/eqmxP; rewrite !(eqmxMr _ (genmxE _)).
apply/genmxP; rewrite genmx_id; congr <<_>>%MS; apply/row_matrixP=> i.
by rewrite !row_mul !mul_rV_lin1 /= hom_envelop_mxC // vec_mxK row_sub.
Qed.

(* The annihilator of a single vector. *)

Definition annihilator_mx u := (E_G :&: kermx (lin_mul_row u))%MS.

Lemma annihilator_mxP : forall u A,
  reflect (A \in E_G /\ u *m A = 0)%MS (A \in annihilator_mx u)%MS.
Proof.
move=> u A; rewrite sub_capmx; apply: (iffP andP) => [[->]|[-> uA0]].
  by move/sub_kermxP; rewrite mul_rV_lin1 /= mxvecK.
by split=> //; apply/sub_kermxP; rewrite mul_rV_lin1 /= mxvecK.
Qed.

(* The subspace of homomorphic images of a row vector.                        *)

Definition row_hom_mx u :=
  (\bigcap_j kermx (vec_mx (row j (annihilator_mx u))))%MS.

Lemma row_hom_mxP : forall u v,
  reflect (exists2 f, u <= dom_hom_mx f & u *m f = v)%MS (v <= row_hom_mx u)%MS.
Proof.
move=> u v; apply: (iffP sub_bigcapmxP) => [iso_uv | [f hom_uf <-] i _].
  have{iso_uv} uv0: forall A, (A \in E_G)%MS /\ u *m A = 0 -> v *m A = 0.
    move=> A; move/annihilator_mxP; case/subsetmxP=> a defA.
    rewrite -[A]mxvecK {A}defA [a *m _]mulmx_sum_row !linear_sum big1 // => i _.
    by rewrite !linearZ /= (sub_kermxP _) ?scalemx0 ?iso_uv.
  pose U := E_G *m lin_mul_row u; pose V :=  E_G *m lin_mul_row v.
  pose f := pinvmx U *m V.
  have hom_uv_f: forall x, x \in G -> u *m rG x *m f = v *m rG x.
    move=> x Gx; apply/eqP; rewrite 2!mulmxA mul_rV_lin1 -subr_eq0 -mulmx_subr.
    rewrite uv0 // 2!linear_sub /= vec_mxK; split.
      by rewrite addmx_sub ?subsetmxMl // eqmx_opp envelop_mx_id.
    have Uux: (u *m rG x <= U)%MS.
      by rewrite -(genmxE U) mxmodule_trans ?cyclic_mx_id ?cyclic_mx_module.
    by rewrite -{2}(mulmxKpV Uux) [_ *m U]mulmxA mul_rV_lin1 subrr.
  have def_uf: u *m f = v by rewrite -[u]mulmx1 -[v]mulmx1 -repr_mx1 hom_uv_f.
  by exists f => //; apply/hom_mxP=> x Gx; rewrite def_uf hom_uv_f.
apply/sub_kermxP; set A := vec_mx _.
have: (A \in annihilator_mx u)%MS by rewrite vec_mxK row_sub.
by case/annihilator_mxP => E_A uA0; rewrite -hom_envelop_mxC // uA0 mul0mx.
Qed.

(* Sub-, isomorphic, simple, semisimple and completely reducible modules.     *)
(* All these predicates are intuitionistic (since, e.g., testing simplicity   *)
(* requires a splitting algorithm fo r the mas field). They are all           *)
(* specialized to square matrices, to avoid spurrrious height parameters.     *)

(* Module isomorphism is an intentional property in general, but it can be    *)
(* decided when one of the two modules is known to be simple.                 *)

CoInductive mx_iso (U V : 'M_n) : Prop :=
  MxIso f of f \in unitmx & (U <= dom_hom_mx f)%MS & (U *m f :=: V)%MS.

Lemma eqmx_iso : forall U V, (U :=: V)%MS -> mx_iso U V.
Proof.
by move=> U V eqUV; exists 1%:M; rewrite ?unitmx1 ?scalar_mx_hom ?mulmx1.
Qed.

Lemma mx_iso_refl : forall U, mx_iso U U.
Proof. by move=> U; exact: eqmx_iso. Qed.

Lemma mx_iso_sym : forall U V, mx_iso U V -> mx_iso V U.
Proof.
move=> U V [f injf homUf defV]; exists (invmx f); first by rewrite unitmx_inv.
  by rewrite dom_hom_invmx // -defV subsetmxMr.
by rewrite -[U](mulmxK injf); exact: eqmxMr (eqmx_sym _).
Qed.

Lemma mx_iso_trans : forall U V W, mx_iso U V -> mx_iso V W -> mx_iso U W.
Proof.
move=> U V W [f injf homUf defV] [g injg homVg defW].
exists (f *m g); first by rewrite unitmx_mul injf.
  by apply/hom_mxP=> x Gx; rewrite !mulmxA 2?(hom_mxP _) ?defV.
by rewrite mulmxA; exact: eqmx_trans (eqmxMr g defV) defW.
Qed.

Lemma mxrank_iso : forall U V, mx_iso U V -> \rank U = \rank V.
Proof. by move=> U V [f injf _ <-]; rewrite mxrankMfree ?row_free_unit. Qed.

Lemma mx_iso_module : forall U V, mx_iso U V -> mxmodule U -> mxmodule V.
Proof.
move=> U V [f _ homUf defV]; rewrite -(eqmx_module defV); exact: hom_mxmodule.
Qed.

(* Simple modules (we reserve the term "irreducible" for representations).    *)

Definition mxsimple (V : 'M_n) :=
  [/\ mxmodule V, V != 0 &
      forall U : 'M_n, mxmodule U -> (U <= V)%MS -> U != 0 -> (U :=: V)%MS].

Definition mxnonsimple (U : 'M_n) :=
  exists V : 'M_n, [&& mxmodule V, (V <= U)%MS, V != 0 & \rank V < \rank U].

Lemma mxsimpleP : forall U,
  [/\ mxmodule U, U != 0 & ~ mxnonsimple U] <-> mxsimple U.
Proof.
move=> U; do [split => [] [modU nzU simU]; split] => // [V modV sVU nzV | [V]].
  apply/eqmxP; apply/idPn; rewrite -(ltn_leqif (mxrank_leqif_eq sVU)) => ltVU.
  by case: simU; exists V; exact/and4P.
by case/and4P=> modV sVU nzV; rewrite simU ?ltnn.
Qed.

Lemma mxsimple_module : forall U, mxsimple U -> mxmodule U.
Proof. by move=> U []. Qed.

Lemma mxsimple_exists : forall m (U : 'M_(m, n)),
  mxmodule U -> U != 0 -> classically (exists2 V, mxsimple V & V <= U)%MS.
Proof.
move=> m U modU nzU [] // simU; move: {2}_.+1 (ltnSn (\rank U)) => r leUr.
elim: r => // r IHr in m U leUr modU nzU simU.
have genU := genmxE U; apply simU; exists <<U>>%MS; last by rewrite genU.
apply/mxsimpleP; split; rewrite ?(eqmx_eq0 genU) ?(eqmx_module genU) //.
case=> V; rewrite !genU; case/and4P=> modV sVU nzV ltVU; case: not_false.
apply: IHr nzV _ => // [|[W simW sWV]]; first exact: leq_trans ltVU _.
by apply: simU; exists W => //; exact: subsetmx_trans sWV sVU.
Qed.

Lemma mx_iso_simple : forall U V, mx_iso U V -> mxsimple U -> mxsimple V.
Proof.
move=> U V isoUV [modU nzU simU]; have [f injf homUf defV] := isoUV.
split=> [||W modW sWV nzW]; first by rewrite (mx_iso_module isoUV).
  by rewrite -(eqmx_eq0 defV) -(mul0mx n f) (can_eq (mulmxK injf)).
apply/eqmxP; rewrite sWV -defV -[W](mulmxKV injf) subsetmxMr //.
set W' := W *m _. 
have sW'U: (W' <= U)%MS by rewrite -[U](mulmxK injf) subsetmxMr ?defV.
rewrite (simU W') //; last by rewrite -(can_eq (mulmxK injf)) mul0mx mulmxKV.
rewrite hom_mxmodule ?dom_hom_invmx // -[W](mulmxKV injf) subsetmxMr //.
exact: subsetmx_trans sW'U homUf.
Qed.

Lemma mxsimple_cyclic : forall u U,
  mxsimple U -> u != 0 -> (u <= U)%MS -> (U :=: cyclic_mx u)%MS.
Proof.
move=> u U [modU _ simU] nz_u Uu; apply/eqmxP; set uG := cyclic_mx u.
have s_uG_U: (uG <= U)%MS by rewrite cyclic_mx_sub.
by rewrite -(simU uG) ?cyclic_mx_eq0 ?subsetmx_refl // cyclic_mx_module.
Qed.

(* The surjective part of Schur's lemma. *)
Lemma mx_Schur_onto : forall m (U : 'M_(m, n)) V f,
    mxmodule U -> mxsimple V -> (U <= dom_hom_mx f)%MS ->
  (U *m f <= V)%MS -> U *m f != 0 -> (U *m f :=: V)%MS.
Proof.
move=> m U V f modU [modV _ simV] homUf sUfV nzUf.
apply: eqmx_trans (eqmx_sym (genmxE _)) _.
apply: simV; rewrite ?(eqmx_eq0 (genmxE _)) ?genmxE //.
by rewrite (eqmx_module (genmxE _)) hom_mxmodule.
Qed.

(* The injective part of Schur's lemma. *)
Lemma mx_Schur_inj : forall U f,
  mxsimple U -> (U <= dom_hom_mx f)%MS -> U *m f != 0 -> (U :&: kermx f)%MS = 0.
Proof.
move=> U f [modU _ simU] homUf nzUf; apply/eqP; apply: contraR nzUf => nz_ker.
rewrite (sameP eqP sub_kermxP) -(simU _ _ _ nz_ker) ?capmxSr ?capmxSl //.
exact: kermx_hom_module.
Qed.

(* The injectve part of Schur's lemma, stated as isomorphism with the image. *)
Lemma mx_Schur_inj_iso : forall U f,
  mxsimple U -> (U <= dom_hom_mx f)%MS -> U *m f != 0 -> mx_iso U (U *m f).
Proof.
move=> U f simU homUf nzUf; have [modU _ _] := simU.
have eqUfU: \rank (U *m f) = \rank U by apply/mxrank_injP; rewrite mx_Schur_inj.
have{eqUfU} [g invg defUf] := complete_unitmx eqUfU.
suffices homUg: (U <= dom_hom_mx g)%MS by exists g; rewrite ?defUf.
apply/hom_mxP=> x Gx; have [ux defUx] := subsetmxP (mxmoduleP modU x Gx).
by rewrite -defUf -(hom_mxP homUf) // defUx -!(mulmxA ux) defUf.
Qed.

(* The isomorphism part of Schur's lemma. *)
Lemma mx_Schur_iso : forall U V f,
    mxsimple U -> mxsimple V -> (U <= dom_hom_mx f)%MS ->
  (U *m f <= V)%MS -> U *m f != 0 -> mx_iso U V.
Proof.
move=> U V f simU simV homUf sUfV nzUf; have [modU _ _] := simU.
have [g invg homUg defUg] := mx_Schur_inj_iso simU homUf nzUf.
exists g => //; apply: mx_Schur_onto; rewrite ?defUg //.
by rewrite -!subsetmx0 defUg in nzUf *. 
Qed.

(* A boolean test for module isomorphism that is only valid for simple        *)
(* modules; this is the only case that matters in practice.                  *)

Lemma nz_row_mxsimple : forall U, mxsimple U -> nz_row U != 0.
Proof. by move=> U [_ nzU _]; rewrite nz_row_eq0. Qed.

Definition mxsimple_iso (U V : 'M_n) :=
  [&& mxmodule V, (V :&: row_hom_mx (nz_row U))%MS != 0 & \rank V <= \rank U].

Lemma mxsimple_isoP : forall U V,
  mxsimple U -> reflect (mx_iso U V) (mxsimple_iso U V).
Proof.
move=> U V simU; pose u := nz_row U.
have [Uu nz_u]: (u <= U)%MS /\ u != 0 by rewrite nz_row_sub nz_row_mxsimple.
apply: (iffP and3P) => [[modV] | isoUV]; last first.
  split; last by rewrite (mxrank_iso isoUV).
    by case: (mx_iso_simple isoUV simU).
  have [f injf homUf defV] := isoUV; apply/rowV0Pn; exists (u *m f).
    rewrite sub_capmx -defV subsetmxMr //.
    by apply/row_hom_mxP; exists f; first exact: (subsetmx_trans Uu).
  by rewrite -(mul0mx _ f) (can_eq (mulmxK injf)) nz_u.
case/rowV0Pn=> v; rewrite sub_capmx; case/andP=> Vv.
case/row_hom_mxP=> f homMf def_v nz_v eqrUV.
pose uG := cyclic_mx u; pose vG := cyclic_mx v.
have def_vG: (uG *m f :=: vG)%MS by rewrite /vG -def_v; exact: hom_cyclic_mx.
have defU: (U :=: uG)%MS by exact: mxsimple_cyclic.
have mod_uG: mxmodule uG by rewrite cyclic_mx_module.
have homUf: (U <= dom_hom_mx f)%MS.
  by rewrite defU cyclic_mx_sub ?dom_hom_mx_module.
have isoUf: mx_iso U (U *m f).
  apply: mx_Schur_inj_iso => //; apply: contra nz_v; rewrite -!subsetmx0.
  by rewrite (eqmxMr f defU) def_vG; exact: subsetmx_trans (cyclic_mx_id v).
apply: mx_iso_trans (isoUf) (eqmx_iso _); apply/eqmxP.
have sUfV: (U *m f <= V)%MS by rewrite (eqmxMr f defU) def_vG cyclic_mx_sub.
by rewrite -mxrank_leqif_eq ?eqn_leq 1?mxrankS // -(mxrank_iso isoUf).
Qed.

Lemma mxsimple_iso_simple : forall U V,
  mxsimple_iso U V -> mxsimple U -> mxsimple V.
Proof.
by move=> U V isoUV simU; apply: mx_iso_simple (simU); exact/mxsimple_isoP.
Qed.

(* For us, "semisimple" means "sum of simple modules"; this is classically,   *)
(* but not intuitionistically, equivalent to the "completely reducible"       *)
(* alternate characterization.                                                *)

Implicit Type I : finType.

CoInductive mxsemisimple (V : 'M_n) :=
  MxSemisimple I U (W := (\sum_(i : I) U i)%MS) of
    forall i, mxsimple (U i) & (W :=: V)%MS & mxdirect W.

(* This is a slight generalization of Aschbacher 12.5 for finite sets. *)
Lemma sum_mxsimple_direct_compl : forall m I W (U : 'M_(m, n)),
    let V := (\sum_(i : I) W i)%MS in
    (forall i : I, mxsimple (W i)) -> mxmodule U -> (U <= V)%MS -> 
  {J : {set I} | let S := U + \sum_(i \in J) W i in S :=: V /\ mxdirect S}%MS.
Proof.
move=> m I W U V simW modU sUV.
pose V_ (J : {set I}) := (\sum_(i \in J) W i)%MS.
pose dxU (J : {set I}) := mxdirect (U + V_ J).
have [J maxJ]: {J | maxset dxU J}; last case/maxsetP: maxJ => dxUVJ maxJ.
  apply: ex_maxset; exists set0.
  by rewrite /dxU mxdirectE /V_ /= !big_set0 addn0 addsmx0 /=.
have modWJ: mxmodule (V_ J) by apply: sumsmx_module => i _; case: (simW i).
exists J; split=> //; apply/eqmxP; rewrite addsmx_sub sUV; apply/andP; split.
  by apply/sumsmx_subP=> i Ji; rewrite (sumsmx_sup i).
rewrite -/(V_ J); apply/sumsmx_subP=> i _.
case Ji: (i \in J).
  by apply: subsetmx_trans (addsmxSr _ _); exact: (sumsmx_sup i).
have [modWi nzWi simWi] := simW i.
rewrite -(simWi (W i :&: (U + V_ J)))%MS ?capmxSl ?capmxSr //.
  by rewrite capmx_module ?addsmx_module.
apply: contraFT (Ji); rewrite negbK => dxWiUVJ.
rewrite -(maxJ (i |: J)) ?setU11 ?subsetUr // /dxU.
rewrite mxdirectE /= !big_setU1 ?Ji //=.
rewrite addnCA addsmxA (addsmxC U) -addsmxA -mxdirectE /=.
by rewrite mxdirect_addsE /= mxdirect_trivial -/(dxU _) dxUVJ.
Qed.

Lemma sum_mxsimple_direct_sub : forall I W (V : 'M_n),
    (forall i : I, mxsimple (W i)) -> (\sum_i W i :=: V)%MS ->
  {J : {set I} | let S := \sum_(i \in J) W i in S :=: V /\ mxdirect S}%MS.
Proof.
move=> I W V simW defV.
have [|J [defS dxS]] := sum_mxsimple_direct_compl simW (mxmodule0 n).
  exact: subset0mx.
exists J; split; last by rewrite mxdirectE /= adds0mx mxrank0 in dxS.
by apply: eqmx_trans defV; rewrite adds0mx_id in defS.
Qed.

Lemma mxsemisimple0 : mxsemisimple 0.
Proof.
exists [finType of 'I_0] (fun _ => 0); [by case | by rewrite big_ord0 | ].
by rewrite mxdirectE /= !big_ord0 mxrank0.
Qed.

Lemma intro_mxsemisimple : forall (I : Type) r (P : pred I) W V,
    (\sum_(i <- r | P i) W i :=: V)%MS ->
    (forall i, P i -> W i != 0 -> mxsimple (W i)) ->
  mxsemisimple V.
Proof.
move=> I r P W V defV simW; pose W_0 := [pred i | W i == 0].
case: (eqVneq V 0) => [-> | nzV]; first exact: mxsemisimple0.
case def_r: r => [| i0 r'] => [|{r' def_r}].
  by rewrite -mxrank_eq0 -defV def_r big_nil mxrank0 in nzV.
move: defV; rewrite (bigID W_0) /= addsmxC -big_filter !(big_nth i0) !big_mkord.
rewrite addsmxC big1 ?adds0mx_id => [|i]; last by case/andP=> _; move/eqP.
set tI := 'I_(_); set r_ := nth _ _ => defV.
have{simW} simWr: forall i : tI, mxsimple (W (r_ i)).
  case=> i; set Pr := fun i => _ => lt_i_r /=.
  suffices: (Pr (r_ i)) by case/andP; exact: simW.
  apply: all_nthP i lt_i_r; apply/all_filterP.
  by rewrite -filter_predI; apply: eq_filter => i; rewrite /= andbb.
have [J []] := sum_mxsimple_direct_sub simWr defV.
case: (set_0Vmem J) => [-> V0 | [j0 Jj0]].
  by rewrite -mxrank_eq0 -V0 big_set0 mxrank0 in nzV.
pose K := {j | j \in J}; pose k0 : K := Sub j0 Jj0.
have bij_KJ: {on J, bijective (sval : K -> _)}.
  by exists (insubd k0) => [k _ | j Jj]; rewrite ?valKd ?insubdK.
have J_K: sval (_ : K) \in J by move=> k; exact: valP k.
rewrite mxdirectE /= !(reindex _ bij_KJ) !(eq_bigl _ _ J_K) -mxdirectE /= -/tI.
exact: MxSemisimple.
Qed.

Lemma mxsimple_semisimple : forall U, mxsimple U -> mxsemisimple U.
Proof.
move=> U simU; apply: (intro_mxsemisimple (_ : \sum_(i < 1) U :=: U))%MS => //.
by rewrite big_ord1.
Qed.

Lemma addsmx_semisimple : forall U V,
  mxsemisimple U -> mxsemisimple V -> mxsemisimple (U + V)%MS.
Proof.
move=> U V [I W /= simW defU _] [J T /= simT defV _].
have defUV: (\sum_ij sum_rect (fun _ => 'M_n) W T ij :=: U + V)%MS.
  by rewrite big_sumType /=; exact: adds_eqmx.
by apply: intro_mxsemisimple defUV _; case=> /=.
Qed.

Lemma sumsmx_semisimple : forall (I : finType) (P : pred I) V,
  (forall i, P i -> mxsemisimple (V i)) -> mxsemisimple (\sum_(i | P i) V i)%MS.
Proof.
move=> I P V ssimV; apply big_prop => //; first exact: mxsemisimple0.
exact: addsmx_semisimple.
Qed.

Lemma eqmx_semisimple : forall U V,
  (U :=: V)%MS -> mxsemisimple U -> mxsemisimple V.
Proof.
move=> U V eqUV [I W S simW defU dxS]; exists I W => //; exact: eqmx_trans eqUV.
Qed.

Lemma hom_mxsemisimple : forall V f : 'M_n,
  mxsemisimple V -> (V <= dom_hom_mx f)%MS -> mxsemisimple (V *m f).
Proof.
move=> V f [I W /= simW defV _]; rewrite -defV; move/sumsmx_subP=> homWf.
have{defV} defVf: (\sum_i W i *m f :=: V *m f)%MS.
  by apply: eqmx_trans (eqmx_sym _) (eqmxMr f defV); exact: sumsmxMr.
apply: (intro_mxsemisimple defVf) => i _ nzWf.
by apply: mx_iso_simple (simW i); apply: mx_Schur_inj_iso; rewrite ?homWf.
Qed.

Lemma mxsemisimple_module : forall U, mxsemisimple U -> mxmodule U.
Proof.
move=> U [I W /= simW defU _].
by rewrite -(eqmx_module defU) sumsmx_module // => i _; case: (simW i).
Qed.

(* Completely reducible modules, and Maeschke's Theorem. *)

CoInductive mxsplits (V U : 'M_n) :=
  MxSplits (W : 'M_n) of mxmodule W & (U + W :=: V)%MS & mxdirect (U + W).

Definition mx_completely_reducible V :=
  forall U, mxmodule U -> (U <= V)%MS -> mxsplits V U.

Lemma mx_reducibleS : forall U V,
    mxmodule U -> (U <= V)%MS ->
  mx_completely_reducible V -> mx_completely_reducible U.
Proof.
move=> U V modU sUV redV U1 modU1 sU1U.
have [W modW defV dxU1W] := redV U1 modU1 (subsetmx_trans sU1U sUV).
exists (W :&: U)%MS; first exact: capmx_module.
  by apply/eqmxP; rewrite !matrix_modl // capmxSr sub_capmx defV sUV /=.
by apply/mxdirect_addsP; rewrite capmxA (mxdirect_addsP dxU1W) cap0mx.
Qed.

Lemma mx_Maeshke : [char F]^'.-group G -> mx_completely_reducible 1%:M.
Proof.
rewrite /pgroup charf'_nat; set nG := _%:R => nzG U; move/mxmoduleP=> Umod _.
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
have tiUker: (U :&: kermx phi = 0)%MS.
  apply/eqP; apply/rowV0P=> v; rewrite sub_capmx; case/andP.
  by case/subsetmxP=> u ->; move/sub_kermxP; rewrite -mulmxA Uphi.
exists (kermx phi); last exact/mxdirect_addsP.
  apply/mxmoduleP=> x Gx; apply/sub_kermxP.
  by rewrite -mulmxA -phiG // mulmxA mulmx_ker mul0mx.
apply/eqmxP; rewrite subsetmx1 subset1mx.
rewrite /row_full mxrank_disjoint_sum //= mxrank_ker.
suffices ->: (U :=: phi)%MS by rewrite subnKC ?rank_leq_row.
apply/eqmxP; rewrite -{1}Uphi subsetmxMl scalemx_sub //.
by rewrite summx_sub // => x Gx; rewrite -mulmxA mulmx_sub ?Umod.
Qed.

Lemma mxsemisimple_reducible : forall V,
  mxsemisimple V -> mx_completely_reducible V.
Proof.
move=> V [I W /= simW defV _] U modU sUV; rewrite -defV in sUV.
have [J [defV' dxV]] := sum_mxsimple_direct_compl simW modU sUV.
exists (\sum_(i \in J) W i)%MS.
- by apply: sumsmx_module => i _; case: (simW i).
- exact: eqmx_trans defV' defV.
by rewrite mxdirect_addsE (sameP eqP mxdirect_addsP) /= in dxV; case/and3P: dxV.
Qed.

Lemma mx_reducible_semisimple : forall V,
  mxmodule V -> mx_completely_reducible V -> classically (mxsemisimple V).
Proof.
move=> V modV redV [] // nssimV; move: {-1}_.+1 (ltnSn (\rank V)) => r leVr.
elim: r => // r IHr in V leVr modV redV nssimV.
case: (eqVneq V 0) => [V0 | nzV].
  by rewrite nssimV ?V0 //; exact: mxsemisimple0.
apply (mxsimple_exists modV nzV) => [[U simU sUV]]; have [modU nzU _] := simU.
have [W modW defUW dxUW] := redV U modU sUV.
have sWV: (W <= V)%MS by rewrite -defUW addsmxSr.
apply: IHr (mx_reducibleS modW sWV redV) _ => // [|ssimW].
  rewrite ltnS -defUW (mxdirectP dxUW) /= in leVr; apply: leq_trans leVr.
  by rewrite -add1n leq_add2r lt0n mxrank_eq0.
apply: nssimV (eqmx_semisimple defUW (addsmx_semisimple _ ssimW)).
exact: mxsimple_semisimple.
Qed.

Lemma mxsemisimpleS : forall U V,
  mxmodule U -> (U <= V)%MS -> mxsemisimple V -> mxsemisimple U.
Proof.
move=> U V modU sUV ssimV.
have [W modW defUW dxUW]:= mxsemisimple_reducible ssimV modU sUV.
move/mxdirect_addsP: dxUW => dxUW.
have defU : (V *m proj_mx U W :=: U)%MS.
  by apply/eqmxP; rewrite proj_mx_sub -{1}[U](proj_mx_id dxUW) ?subsetmxMr.
apply: eqmx_semisimple defU _; apply: hom_mxsemisimple ssimV _.
by rewrite -defUW proj_mx_hom.
Qed.

Lemma hom_mxsemisimple_iso : forall I P U W f,
  let V := (\sum_(i : I |  P i) W i)%MS in
  mxsimple U -> (forall i, P i -> W i != 0 -> mxsimple (W i)) -> 
  (V <= dom_hom_mx f)%MS -> (U <= V *m f)%MS ->
  {i | P i & mx_iso (W i) U}.
Proof.
move=> I P U W f V simU simW homVf sUVf; have [modU nzU _] := simU.
have ssimVf: mxsemisimple (V *m f).
  by apply: hom_mxsemisimple homVf; exact: intro_mxsemisimple simW.
have [U' modU' defVf] := mxsemisimple_reducible ssimVf modU sUVf.
move/mxdirect_addsP=> dxUU'; pose p := f *m proj_mx U U'.
case: (pickP (fun i => P i && (W i *m p != 0))) => [i | no_i].
  case/andP=> Pi nzWip; exists i => //.
  have sWiV: (W i <= V)%MS by rewrite (sumsmx_sup i).
  have sWipU: (W i *m p <= U)%MS by rewrite mulmxA proj_mx_sub.
  apply: (mx_Schur_iso (simW i Pi _) simU _ sWipU nzWip).
    by apply: contra nzWip; move/eqP->; rewrite mul0mx.
  apply: (subsetmx_trans sWiV); apply/hom_mxP=> x Gx.
  by rewrite mulmxA [_ *m p]mulmxA 2?(hom_mxP _) -?defVf ?proj_mx_hom.
case/negP: nzU; rewrite -subsetmx0 -[U](proj_mx_id dxUU') //.
rewrite (subsetmx_trans (subsetmxMr _ sUVf)) // -mulmxA -/p sumsmxMr.
by apply/sumsmx_subP=> i Pi; move/negbT: (no_i i); rewrite Pi negbK subsetmx0.
Qed.

(* The component associated to a given irreducible module.                    *)

Section Components.

Fact component_mx_key : unit. Proof. by []. Qed.
Local Notation component_mx_expr U :=
  (\sum_i cyclic_mx (row i (row_hom_mx (nz_row U))))%MS.
Definition component_mx :=
  let: tt := component_mx_key in fun U : 'M[F]_n => component_mx_expr U.

Variable U : 'M[F]_n.
Hypothesis simU : mxsimple U.

Let u := nz_row U.
Let iso_u := row_hom_mx u.
Let nz_u : u != 0 := nz_row_mxsimple simU.
Let Uu : (u <= U)%MS := nz_row_sub U.
Let defU : (U :=: cyclic_mx u)%MS := mxsimple_cyclic simU nz_u Uu.
Local Notation compU := (component_mx U).

Lemma component_mxE : compU = component_mx_expr U.
Proof. by rewrite /component_mx; case component_mx_key. Qed.

Lemma component_mx_module : mxmodule compU.
Proof.
by rewrite component_mxE sumsmx_module // => i; rewrite cyclic_mx_module.
Qed.

Lemma genmx_component : <<compU>>%MS = compU.
Proof.
by rewrite component_mxE genmx_sums; apply: eq_bigr => i; rewrite genmx_id.
Qed.

Lemma component_mx_def : {I : finType & {W : I -> 'M_n |
  forall i, mx_iso U (W i) & compU = \sum_i W i}}%MS.
Proof.
pose r i := row i iso_u; pose r_nz i := r i != 0; pose I := {i | r_nz i}.
exists [finType of I]; exists (fun i => cyclic_mx (r (sval i))) => [i|].
  apply/mxsimple_isoP=> //; apply/and3P.
  split; first by rewrite cyclic_mx_module.
    apply/rowV0Pn; exists (r (sval i)); last exact: (svalP i).
    by rewrite sub_capmx cyclic_mx_id row_sub.
  have [f hom_u_f <-] := @row_hom_mxP u (r (sval i)) (row_sub _ _).
  by rewrite defU -hom_cyclic_mx ?mxrankM_maxl.
rewrite -(eq_bigr _ (fun _ _ => genmx_id _)) -genmx_sums -genmx_component.
rewrite component_mxE; apply/genmxP; apply/andP; split; last first.
  by apply/sumsmx_subP => i _; rewrite (sumsmx_sup (sval i)).
apply/sumsmx_subP => i _.
case i0: (r_nz i); first by rewrite (sumsmx_sup (Sub i i0)).
by move/negbFE: i0; rewrite -cyclic_mx_eq0; move/eqP->; exact: subset0mx.
Qed.

Lemma component_mx_semisimple : mxsemisimple compU.
Proof.
have [I [W isoUW ->]] := component_mx_def.
apply: intro_mxsemisimple (eqmx_refl _) _ => i _ _.
exact: mx_iso_simple (isoUW i) simU.
Qed.

Lemma mx_iso_component : forall V, mx_iso U V -> (V <= compU)%MS.
Proof.
move=> V isoUV; have simV := mx_iso_simple isoUV simU.
have [f injf homUf defV] := isoUV.
have hom_u_f := subsetmx_trans Uu homUf.
have ->: (V :=: cyclic_mx (u *m f))%MS.
  apply: eqmx_trans (hom_cyclic_mx hom_u_f).
  exact: eqmx_trans (eqmx_sym defV) (eqmxMr _ defU).
have iso_uf: (u *m f <= iso_u)%MS by apply/row_hom_mxP; exists f.
rewrite genmxE; apply/row_subP=> j; rewrite row_mul mul_rV_lin1 /=.
set a := vec_mx _; apply: subsetmx_trans (subsetmxMr _ iso_uf) _.
apply/row_subP=> i; rewrite row_mul component_mxE (sumsmx_sup i) //.
by apply/cyclic_mxP; exists a; rewrite // vec_mxK row_sub.
Qed.

Lemma component_mx_id : (U <= compU)%MS.
Proof. exact: mx_iso_component (mx_iso_refl U). Qed.

Lemma hom_component_mx_iso : forall f V,
    mxsimple V -> (compU <= dom_hom_mx f)%MS -> (V <= compU *m f)%MS ->
  mx_iso U V.
Proof.
have [I [W isoUW ->]] := component_mx_def; move=> f V simV homWf sVWf.
have [i _ _|i _ ] := hom_mxsemisimple_iso simV _ homWf sVWf.
  exact: mx_iso_simple (simU).
exact: mx_iso_trans. 
Qed.


Lemma component_mx_iso : forall V, mxsimple V -> (V <= compU)%MS -> mx_iso U V.
Proof.
move=> V simV; rewrite -[compU]mulmx1.
exact: hom_component_mx_iso (scalar_mx_hom _ _).
Qed.

Lemma hom_component_mx : forall f,
  (compU <= dom_hom_mx f)%MS -> (compU *m f <= compU)%MS.
Proof.
move=> f hom_f.
have [I W /= simW defW _] := hom_mxsemisimple component_mx_semisimple hom_f.
rewrite -defW; apply/sumsmx_subP=> i _; apply: mx_iso_component.
by apply: hom_component_mx_iso hom_f _ => //; rewrite -defW (sumsmx_sup i).
Qed.

End Components.

Lemma component_mx_isoP : forall U V,
    mxsimple U -> mxsimple V ->
  reflect (mx_iso U V) (component_mx U == component_mx V).
Proof.
move=> U V simU simV; apply: (iffP eqP) => isoUV.
  by apply: component_mx_iso; rewrite ?isoUV ?component_mx_id.
rewrite -(genmx_component U) -(genmx_component V); apply/genmxP.
wlog: U V simU simV isoUV / ~~ (component_mx U <= component_mx V)%MS.
  move=> IH; apply: wlog_neg; case/nandP; first exact: IH.
  by rewrite andbC; apply: IH => //; exact: mx_iso_sym.
case/negP; have [I [W isoWU ->]] := component_mx_def simU.
apply/sumsmx_subP => i _; apply: mx_iso_component => //.
exact: mx_iso_trans (mx_iso_sym isoUV) (isoWU i).
Qed.

Lemma component_mx_disjoint : forall U V,
    mxsimple U -> mxsimple V -> component_mx U != component_mx V ->
  (component_mx U :&: component_mx V = 0)%MS.
Proof.
move=> U V simU simV neUV; apply/eqP; apply: contraR neUV => ntUV.
apply: (mxsimple_exists _ ntUV) => [|[W simW]].
  by rewrite capmx_module ?component_mx_module.
rewrite sub_capmx; case/andP=> sWU sWV.
apply/component_mx_isoP=> //.
by apply: mx_iso_trans (_ : mx_iso U W) (mx_iso_sym _); exact: component_mx_iso.
Qed.

Section Socle.

Record socleType := EnumSocle {
  socle_base_enum : seq 'M[F]_n;
  _ : forall M, M \in socle_base_enum -> mxsimple M;
  _ : forall M, mxsimple M -> has (mxsimple_iso M) socle_base_enum
}.

Lemma socle_exists : classically socleType.
Proof.
pose V : 'M[F]_n := 0; have: mxsemisimple V by exact: mxsemisimple0.
have: n - \rank V < n.+1 by rewrite mxrank0 subn0.
elim: _.+1 V => // n' IHn' V; rewrite ltnS => le_nV_n' ssimV.
case=> // maxV; apply maxV; have [I /= U simU defV _] := ssimV.
exists (map U (enum I)) => [M | M simM]; first by case/mapP=> i _ ->.
suffices sMV: (M <= V)%MS.
  rewrite -defV -(mulmx1 (\sum_i _)%MS) in sMV.
  have [//| i _] := hom_mxsemisimple_iso simM _ (scalar_mx_hom _ _) sMV.
  move/mx_iso_sym=> isoM; rewrite has_map; apply/hasP.
  by exists i; [exact: mem_enum | exact/mxsimple_isoP].
have ssimMV := addsmx_semisimple (mxsimple_semisimple simM) ssimV.
apply: contraLR is_true_true => nsMV; apply: IHn' ssimMV _ maxV.
apply: leq_trans le_nV_n'; rewrite ltn_sub2l //.
  rewrite ltn_neqAle rank_leq_row andbT -[_ == _]subset1mx.
  apply: contra nsMV; apply: subsetmx_trans; exact: subsetmx1.
rewrite (ltn_leqif (mxrank_leqif_sup _)) ?addsmxSr //.
by rewrite addsmx_sub subsetmx_refl andbT.
Qed.

Section SocleDef.

Variable sG0 : socleType.

Definition socle_enum := map component_mx (socle_base_enum sG0).

Lemma component_socle : forall M, mxsimple M -> component_mx M \in socle_enum.
Proof.
rewrite /socle_enum; case: sG0 => e0 /= sim_e mem_e M simM.
case/hasP: (mem_e M simM) => M' e0M' isoMM'; apply/mapP; exists M' => //.
by apply/eqP; apply/component_mx_isoP; [|exact: sim_e | exact/mxsimple_isoP].
Qed.

Inductive socle_sort : predArgType := PackSocle W of W \in socle_enum.

Local Notation sG := socle_sort.
Local Notation e0 := (socle_base_enum sG0).

Definition socle_base W := let: PackSocle W _ := W in e0`_(index W socle_enum).

Coercion socle_val W : 'M[F]_n := component_mx (socle_base W).

Lemma socle_simple : forall W, mxsimple (socle_base W).
Proof.
case=> M; rewrite /= /socle_enum /=; case: sG0 => e sim_e _ /= e_M.
by apply: sim_e; rewrite mem_nth // -(size_map component_mx) index_mem.
Qed.

Definition socle_module (i : sG) := mxsimple_module (socle_simple i).

Definition socle_repr i := submod_repr (socle_module i).

Lemma nz_socle : forall W : sG, W != 0 :> 'M_n.
Proof.
move=> W; have simW := socle_simple W.
have [_ nzW _] := simW; apply: contra nzW; rewrite -!subsetmx0.
exact: subsetmx_trans (component_mx_id simW).
Qed.

Lemma socle_mem : forall W : sG, (W : 'M_n) \in socle_enum.
Proof. by move=> W; exact: component_socle (socle_simple _). Qed.

Lemma PackSocleK : forall W e0W, @PackSocle W e0W = W :> 'M_n.
Proof.
rewrite /socle_val /= => W e0W; rewrite -(nth_map _ 0) ?nth_index //.
by rewrite -(size_map component_mx) index_mem.
Qed.

Canonical Structure socle_subType :=
  SubType _ _ _ socle_sort_rect PackSocleK.
Definition socle_eqMixin := Eval hnf in [eqMixin of sG by <:].
Canonical Structure socle_eqType := Eval hnf in EqType sG socle_eqMixin.
Definition socle_choiceMixin := Eval hnf in [choiceMixin of sG by <:].
Canonical Structure socle_choiceType := ChoiceType sG socle_choiceMixin.

Lemma socleP : forall W W' : sG, reflect (W = W') (W == W')%MS.
Proof.
by move=> W W'; rewrite (sameP genmxP eqP) !{1}genmx_component; exact: (W =P _).
Qed.

Fact socle_finType_subproof :
  cancel (fun W => SeqSub (socle_mem W)) (fun s => PackSocle (valP s)).
Proof. by move=> W /=; apply: val_inj; rewrite /= PackSocleK. Qed.

Definition socle_countMixin := CanCountMixin socle_finType_subproof.
Canonical Structure socle_countType := CountType sG socle_countMixin.
Canonical Structure socle_subCountType := [subCountType of sG].
Definition socle_finMixin := CanFinMixin socle_finType_subproof.
Canonical Structure socle_finType := FinType sG socle_finMixin.
Canonical Structure socle_subFinType := [subFinType of sG].

End SocleDef.

Identity Coercion Type_of_predArgType : predArgType >-> Sortclass.
Coercion socle_sort : socleType >-> predArgType.

Variable sG : socleType.

Section SubSocle.

Variable P : pred sG.
Notation S := (\sum_(W : sG | P W) socle_val W)%MS.

Lemma subSocle_module : mxmodule S.
Proof. by rewrite sumsmx_module // => W _; exact: component_mx_module. Qed.

Lemma subSocle_semisimple : mxsemisimple S.
Proof.
apply: sumsmx_semisimple => W _; apply: component_mx_semisimple.
exact: socle_simple.
Qed.
Local Notation ssimS := subSocle_semisimple.

Lemma subSocle_iso : forall M,
  mxsimple M -> (M <= S)%MS -> {W : sG | P W & mx_iso (socle_base W) M}.
Proof.
move=> M simM sMS; have [modM nzM _] := simM.
have [V /= modV defMV] := mxsemisimple_reducible ssimS modM sMS.
move/mxdirect_addsP=> dxMV; pose p := proj_mx M V; pose Sp (W : sG) := W *m p.
case: (pickP [pred i | P i && (Sp i != 0)]) => [/= W | Sp0]; last first.
  case/negP: nzM; rewrite -subsetmx0 -[M](proj_mx_id dxMV) //.
  rewrite (subsetmx_trans (subsetmxMr _ sMS)) // sumsmxMr big1 // => W P_W.
  by apply/eqP; move/negbT: (Sp0 W); rewrite /= P_W negbK.
rewrite {}/Sp /=; case/andP=> P_W nzSp; exists W => //.
have homWp: (W <= dom_hom_mx p)%MS.
  apply: subsetmx_trans (proj_mx_hom dxMV modM modV).
  by rewrite defMV (sumsmx_sup W).
have simWP := socle_simple W; apply: hom_component_mx_iso (homWp) _ => //.
by rewrite (mx_Schur_onto _ simM) ?proj_mx_sub ?component_mx_module.
Qed.

Lemma capmx_subSocle : forall m (M : 'M_(m, n)),
  mxmodule M -> (M :&: S :=: \sum_(W : sG | P W) (M :&: W))%MS.
Proof.
move=> m M modM; apply/eqmxP; apply/andP; split; last first.
  by apply/sumsmx_subP=> W P_W; rewrite capmxS // (sumsmx_sup W).
have modMS: mxmodule (M :&: S)%MS by rewrite capmx_module ?subSocle_module.
have [J /= U simU defMS _] := mxsemisimpleS modMS (capmxSr M S) ssimS.
rewrite -defMS; apply/sumsmx_subP=> j _.
have [sUjV sUjS]: (U j <= M /\ U j <= S)%MS.
  by apply/andP; rewrite -sub_capmx -defMS (sumsmx_sup j). 
have [W P_W isoWU] := subSocle_iso (simU j) sUjS.
rewrite (sumsmx_sup W) // sub_capmx sUjV mx_iso_component //.
exact: socle_simple.
Qed.

End SubSocle.

Lemma subSocle_direct : forall P, mxdirect (\sum_(W : sG | P W) W).
Proof.
move=> P; apply/mxdirect_sumsP=> W _; apply/eqP.
rewrite -subsetmx0 capmx_subSocle ?component_mx_module //.
apply/sumsmx_subP=> W'; case/andP=> _ neWW'.
by rewrite capmxC component_mx_disjoint //; exact: socle_simple.
Qed.

Definition Socle := (\sum_(W : sG) W)%MS.

Lemma simple_Socle : forall M, mxsimple M -> (M <= Socle)%MS.
Proof.
move=> M simM; have socM := component_socle sG simM.
by rewrite (sumsmx_sup (PackSocle socM)) // PackSocleK component_mx_id.
Qed.

Lemma semisimple_Socle : forall U, mxsemisimple U -> (U <= Socle)%MS.
Proof.
by move=> _ [I M /= simM <- _]; apply/sumsmx_subP=> i _; exact: simple_Socle.
Qed.

Lemma reducible_Socle : forall U,
  mxmodule U -> mx_completely_reducible U -> (U <= Socle)%MS.
Proof.
move=> U modU redU; apply: (mx_reducible_semisimple modU redU).
exact: semisimple_Socle.
Qed.

Lemma genmx_Socle : <<Socle>>%MS = Socle.
Proof. by rewrite genmx_sums; apply: eq_bigr => W; rewrite genmx_component. Qed.

Lemma reducible_Socle1 : mx_completely_reducible 1%:M -> Socle = 1%:M.
Proof.
move=> redG; rewrite -genmx1 -genmx_Socle; apply/genmxP.
by rewrite subsetmx1 reducible_Socle ?mxmodule1.
Qed.

Lemma Socle_module : mxmodule Socle. Proof. exact: subSocle_module. Qed.

Lemma Socle_semisimple : mxsemisimple Socle.
Proof. exact: subSocle_semisimple. Qed.

Lemma Socle_direct : mxdirect Socle. Proof. exact: subSocle_direct. Qed.

Lemma Socle_iso : forall M, mxsimple M -> {W : sG | mx_iso (socle_base W) M}.
Proof.
by move=> M simM; case/subSocle_iso: (simple_Socle simM) => // W _; exists W.
Qed.

End Socle.

(* Centralizer subgroup and central homomorphisms. *)
Section CentHom.

Variable f : 'M[F]_n.

Definition rcent := [set x \in G | f *m rG x == rG x *m f].

Lemma rcent_sub : rcent \subset G.
Proof. by apply/subsetP=> x; case/setIdP. Qed.

Lemma rcent_group_set : group_set rcent.
Proof.
apply/group_setP; rewrite inE group1 repr_mx1 mulmx1 mul1mx; split=> //= x y.
case/setIdP=> Gx; move/eqP=> cfx; case/setIdP=> Gy; move/eqP=> cfy.
by rewrite inE repr_mxM ?groupM //= -mulmxA -cfy !mulmxA cfx.
Qed.
Canonical Structure rcent_group := Group rcent_group_set.

Definition centgmx := G \subset rcent.

Lemma centgmxP : reflect (forall x, x \in G -> f *m rG x = rG x *m f) centgmx.
Proof.
apply: (iffP subsetP) => cGf x Gx;
  by have:= cGf x Gx; rewrite !inE Gx /=; move/eqP.
Qed.

Lemma row_full_dom_hom : row_full (dom_hom_mx f) = centgmx.
Proof.
rewrite -subset1mx.
by apply/hom_mxP/centgmxP=> cfG x; move/cfG; rewrite !mul1mx.
Qed.

Lemma memmx_cent_envelop : (f \in 'C(E_G))%MS = centgmx.
Proof.
apply/cent_rowP/centgmxP=> [cfG x Gx | cfG i].
  by have:= cfG (enum_rank_in Gx x); rewrite rowK mxvecK enum_rankK_in.
by rewrite rowK mxvecK /= cfG ?enum_valP.
Qed.

Lemma kermx_centg_module : centgmx -> mxmodule (kermx f).
Proof.
move/centgmxP=> cGf; apply/mxmoduleP=> x Gx; apply/sub_kermxP.
by rewrite -mulmxA -cGf // mulmxA mulmx_ker mul0mx.
Qed.

Lemma centgmx_hom : forall m (U : 'M_(m, n)),
  centgmx -> (U <= dom_hom_mx f)%MS.
Proof.
move=> m U; rewrite -row_full_dom_hom -subset1mx.
exact: subsetmx_trans (subsetmx1 _).
Qed.

End CentHom.

(* Representation kernel, and faithful representations. *)

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

(* (Globally) irreducible, and absolutely irreducible representations. Note   *)
(* that unlike "reducible", "absolutely irreducible" can easily be decided.   *)

Definition mx_irreducible := mxsimple 1%:M.

Lemma mx_irrP :
  mx_irreducible <-> n > 0 /\ (forall U, @mxmodule n U -> U != 0 -> row_full U).
Proof.
rewrite /mx_irreducible /mxsimple mxmodule1 -mxrank_eq0 mxrank1 -lt0n.
do [split=> [[_ -> irrG] | [-> irrG]]; split=> // U] => [modU | [modU _]] nzU.
  by rewrite -subset1mx (irrG U) ?subsetmx1.
by apply/eqmxP; rewrite subsetmx1 subset1mx irrG.
Qed.

(* Schur's lemma for endomorphisms. *)
Lemma mx_Schur :
  mx_irreducible -> forall f, centgmx f -> f != 0 -> f \in unitmx.
Proof.
move/mx_Schur_onto=> irrG f.
rewrite -row_full_dom_hom -!row_full_unit -!subset1mx => cGf nz.
by rewrite -[f]mul1mx irrG ?subsetmx1 ?mxmodule1 ?mul1mx.
Qed.

Definition mx_absolutely_irreducible := (n > 0) && row_full E_G.

Lemma mx_abs_irrP :
  reflect (n > 0 /\ exists a_, forall A, A = \sum_(x \in G) a_ x A *m: rG x)
          mx_absolutely_irreducible.
Proof.
have G_1 := group1 G; have bijG := enum_val_bij_in G_1.
set h := enum_val in bijG; have Gh : h _ \in G by exact: enum_valP.
rewrite /mx_absolutely_irreducible; case: (n > 0); last by right; case.
apply: (iffP row_fullP) => [[E' E'G] | [_ [a_ a_G]]].
  split=> //; exists (fun x B => (mxvec B *m E') 0 (enum_rank_in G_1 x)) => B.
  apply: (can_inj mxvecK); rewrite -{1}[mxvec B]mulmx1 -{}E'G mulmxA.
  move: {B E'}(_ *m E') => u; apply/rowP=> j.
  rewrite linear_sum (reindex h) //= mxE summxE.
  by apply: eq_big => [k| k _]; rewrite ?Gh // enum_valK_in mxE linearZ !mxE.
exists (\matrix_(j, i) a_ (h i) (vec_mx (row j 1%:M))).
apply/row_matrixP=> i; rewrite -[row i 1%:M]vec_mxK {}[vec_mx _]a_G.
apply/rowP=> j; rewrite linear_sum (reindex h) //= 2!mxE summxE.
by apply: eq_big => [k| k _]; [rewrite Gh | rewrite linearZ !mxE].
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

Lemma mx_abs_irrW : mx_absolutely_irreducible -> mx_irreducible.
Proof.
case/mx_abs_irrP=> n_gt0 [a_ a_G]; apply/mx_irrP; split=> // U Umod.
case/rowV0Pn=> u Uu; rewrite -mxrank_eq0 -lt0n row_leq_rank -subset1mx.
case/subsetmxP: Uu => v ->{u}; case/row_freeP=> u' vK; apply/row_subP=> i.
rewrite rowE scalar_mxC -{}vK -2!mulmxA; move: {u' i}(u' *m _) => A.
rewrite mulmx_sub {v}// [A]a_G linear_sum summx_sub //= => x Gx.
by rewrite linearZ /= scalemx_sub // (mxmoduleP Umod).
Qed.

Lemma linear_mx_abs_irr : n = 1%N -> mx_absolutely_irreducible.
Proof.
move=> n1; rewrite /mx_absolutely_irreducible /row_full eqn_leq rank_leq_col.
rewrite {1 2 3}n1 /= lt0n mxrank_eq0; apply/eqP=> E0; case/idPn: envelop_mx1.
by rewrite E0 eqmx0 subsetmx0 mxvec_eq0 -mxrank_eq0 mxrank1 n1.
Qed.

Lemma rker_linear : n = 1%N -> G^`(1)%g \subset rker.
Proof.
move=> n1; rewrite gen_subG; apply/subsetP=> xy; case/imset2P=> x y Gx Gy ->.
rewrite !inE groupR //= /commg mulgA -invMg repr_mxM ?groupV ?groupM //.
rewrite mulmxA (can2_eq (repr_mxK _) (repr_mxKV _)) ?groupM //.
rewrite !repr_mxV ?repr_mxM ?groupM //; move: (rG x) (rG y).
by rewrite n1 => rx ry; rewrite (mx11_scalar rx) scalar_mxC.
Qed.

Lemma abelian_abs_irr : abelian G -> mx_absolutely_irreducible = (n == 1%N).
Proof.
move=> cGG; apply/idP/eqP=> [absG|]; last exact: linear_mx_abs_irr.
have [n_gt0 _] := andP absG.
pose M := <<delta_mx 0 (Ordinal n_gt0) : 'rV[F]_n>>%MS.
have rM: \rank M = 1%N by rewrite genmxE mxrank_delta.
suffices defM: (M :=: 1%:M)%MS by rewrite defM mxrank1 in rM.
case: (mx_abs_irrW absG) => _ _; apply; rewrite ?subsetmx1 -?mxrank_eq0 ?rM //.
apply/mxmoduleP=> x Gx; suffices: is_scalar_mx (rG x).
  by case/is_scalar_mxP=> a ->; rewrite mul_mx_scalar scalemx_sub.
apply: (mx_abs_irr_cent_scalar absG). 
by apply/centgmxP=> y Gy; rewrite -!repr_mxM // (centsP cGG).
Qed.

End OneRepresentation.

Implicit Arguments mxmoduleP [gT G n rG m U].
Implicit Arguments envelop_mxP [gT G n rG A].
Implicit Arguments hom_mxP [gT G n rG m f W].
Implicit Arguments rfix_mxP [gT G n rG m W].
Implicit Arguments cyclic_mxP [gT G n rG u v].
Implicit Arguments annihilator_mxP [gT G n rG u A].
Implicit Arguments row_hom_mxP [gT G n rG u v].
Implicit Arguments mxsimple_isoP [gT G n rG U V].
Implicit Arguments socleP [gT G n rG sG0 W W'].
Implicit Arguments centgmxP [gT G n rG f].
Implicit Arguments rkerP [gT G n rG x].
Implicit Arguments mx_abs_irrP [gT G n rG].

Implicit Arguments val_submod_inj [n U m].
Implicit Arguments val_factmod_inj [n U m].

Prenex Implicits val_submod_inj val_factmod_inj.

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

Lemma envelop_mx_ring : mxring (enveloping_algebra_mx rG).
Proof.
apply/andP; split; first by apply/mulsmx_subP; exact: envelop_mxM.
apply/mxring_idP; exists 1%:M; split=> *; rewrite ?mulmx1 ?mul1mx //.
  by rewrite -mxrank_eq0 mxrank1.
exact: envelop_mx1.
Qed.

End Proper.

Section JacobsonDensity.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variable rG : mx_representation G n.
Hypothesis irrG : mx_irreducible rG.

Local Notation E_G := (enveloping_algebra_mx rG).
Local Notation Hom_G := 'C(E_G)%MS.

Lemma mx_Jacobson_density : ('C(Hom_G) <= E_G)%MS.
Proof.
apply/row_subP=> iB; rewrite -[row iB _]vec_mxK; move defB: (vec_mx _) => B.
have{defB} cBcE: (B \in 'C(Hom_G))%MS by rewrite -defB vec_mxK row_sub.
have rGnP: mx_repr G (fun x => lin_mx (mulmxr (rG x)) : 'A_n).
  split=> [|x y Gx Gy]; apply/row_matrixP=> i.
    by rewrite !rowE mul_rV_lin repr_mx1 /= !mulmx1 vec_mxK.
  by rewrite !rowE mulmxA !mul_rV_lin repr_mxM //= mxvecK mulmxA.
move def_rGn: (MxRepresentation rGnP) => rGn.
pose E_Gn := enveloping_algebra_mx rGn.
pose e1 : 'rV[F]_(n ^ 2) := mxvec 1%:M; pose U := cyclic_mx rGn e1.
have U_e1: (e1 <= U)%MS by rewrite cyclic_mx_id.
have modU: mxmodule rGn U by rewrite cyclic_mx_module.
pose Bn : 'M_(n ^ 2) := lin_mx (mulmxr B).
suffices U_e1Bn: (e1 *m Bn <= U)%MS.
  rewrite mul_vec_lin /= mul1mx in U_e1Bn; apply: subsetmx_trans U_e1Bn _.
  rewrite genmxE; apply/row_subP=> i; rewrite row_mul rowK mul_vec_lin_row.
  by rewrite -def_rGn mul_vec_lin /= mul1mx (eq_row_sub i) ?rowK.
have{cBcE} cBncEn: forall A, centgmx rGn A -> A *m Bn = Bn *m A.
  rewrite -def_rGn => A cAG; apply/row_matrixP; case/mxvec_indexP=> j k.
  rewrite !rowE !mulmxA -mxvec_delta -(mul_delta_mx (0 : 'I_1)).
  rewrite mul_rV_lin mul_vec_lin /= -mulmxA; apply: (canLR vec_mxK).
  apply/row_matrixP=> i; set dj0 := delta_mx j 0.
  pose Aij := row i \o vec_mx \o mulmxr A \o mxvec \o mulmx dj0.
  have defAij := mul_rV_lin1 [linear of Aij]; rewrite /= {2}/Aij /= in defAij.
  rewrite -defAij row_mul -defAij -!mulmxA (cent_mxP cBcE) {k}//.
  rewrite memmx_cent_envelop; apply/centgmxP=> x Gx; apply/row_matrixP=> k.
  rewrite !row_mul !rowE !{}defAij /= -row_mul mulmxA mul_delta_mx.
  congr (row i _); rewrite -(mul_vec_lin (mulmxr_linear _ _)) -mulmxA.
  by rewrite -(centgmxP cAG) // mulmxA mx_rV_lin.
suffices redGn: mx_completely_reducible rGn 1%:M.
  have [V modV defUV] := redGn _ modU (subsetmx1 _); move/mxdirect_addsP=> dxUV.
  rewrite -(proj_mx_id dxUV U_e1) -mulmxA {}cBncEn 1?mulmxA ?proj_mx_sub //.
  by rewrite -row_full_dom_hom -subset1mx -defUV proj_mx_hom.
pose W i : 'M[F]_(n ^ 2) := <<lin1_mx (mxvec \o mulmx (delta_mx i 0))>>%MS.
have defW: (\sum_i W i :=: 1%:M)%MS.
  apply/eqmxP; rewrite subsetmx1; apply/row_subP; case/mxvec_indexP=> i j.
  rewrite row1 -mxvec_delta (sumsmx_sup i) // genmxE; apply/subsetmxP.
  by exists (delta_mx 0 j); rewrite mul_rV_lin1 /= mul_delta_mx.
apply: mxsemisimple_reducible; apply: (intro_mxsemisimple defW) => i _ nzWi.
split=> // [|Vi modVi sViWi nzVi].
  apply/mxmoduleP=> x Gx; rewrite genmxE (eqmxMr _ (genmxE _)) -def_rGn.
  apply/row_subP=> j; rewrite rowE mulmxA !mul_rV_lin1 /= mxvecK -mulmxA.
  by apply/subsetmxP; move: (_ *m rG x) => v; exists v; rewrite mul_rV_lin1.
apply/eqmxP; do [rewrite !genmxE; set f := lin1_mx _] in sViWi *.
have f_free: row_free f.
  apply/row_freeP; exists (lin1_mx (row i \o vec_mx)); apply/row_matrixP=> j.
  by rewrite row1 rowE mulmxA !mul_rV_lin1 /= mxvecK rowE !mul_delta_mx.
pose V := <<Vi *m pinvmx f>>%MS; have Vidf := mulmxKpV sViWi.
suffices V1: (V :=: 1%:M)%MS.
  by rewrite sViWi -[f]mul1mx -Vidf subsetmxMr // -V1 genmxE.
case: irrG => _ _; apply; rewrite ?subsetmx1 //; last first.
  by rewrite -mxrank_eq0 genmxE -(mxrankMfree _ f_free) Vidf mxrank_eq0.
apply/mxmoduleP=> x Gx; rewrite genmxE (eqmxMr _ (genmxE _)).
rewrite -(subsetmxMfree _ _ f_free) Vidf.
apply: subsetmx_trans (mxmoduleP modVi x Gx); rewrite -{2}Vidf.
apply/row_subP=> j; apply: (eq_row_sub j); rewrite row_mul -def_rGn.
by rewrite !(row_mul _ _ f) !mul_rV_lin1 /= mxvecK !row_mul !mulmxA.
Qed.

Lemma cent_mx_scalar_abs_irr : \rank Hom_G <= 1 -> mx_absolutely_irreducible rG.
Proof.
rewrite leqNgt; move/(has_non_scalar_mxP (scalar_mx_cent _ _)) => scal_cE.
apply/andP; split; first by case/mx_irrP: irrG.
rewrite -subset1mx; apply: subsetmx_trans mx_Jacobson_density.
apply/memmx_subP=> B _; apply/cent_mxP=> A cGA.
case scalA: (is_scalar_mx A); last by case: scal_cE; exists A; rewrite ?scalA.
by case/is_scalar_mxP: scalA => a ->; rewrite scalar_mxC.
Qed.

End JacobsonDensity.

Section ChangeGroup.

Variables (gT : finGroupType) (G H : {group gT}) (n : nat).
Variables (rG : mx_representation G n).

Section SubGroup.

Hypothesis sHG : H \subset G.

Lemma subg_mx_repr : mx_repr H rG.
Proof.
by split=> [|x y Hx Hy]; rewrite (repr_mx1, repr_mxM) ?(subsetP sHG).
Qed.
Definition subg_repr := MxRepresentation subg_mx_repr.
Local Notation rH := subg_repr.

Lemma rfix_subg : rfix_mx rH = rfix_mx rG. Proof. by []. Qed.

Lemma rcent_subg : forall U, rcent rH U = H :&: rcent rG U.
Proof.
by move=> U; apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG).
Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstab_subg : rstab rH U = H :&: rstab rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

Lemma rstabs_subg : rstabs rH U = H :&: rstabs rG U.
Proof. by apply/setP=> x; rewrite !inE andbA -in_setI (setIidPl sHG). Qed.

Lemma mxmodule_subg : mxmodule rG U -> mxmodule rH U.
Proof. by rewrite /mxmodule rstabs_subg subsetI subxx; exact: subset_trans. Qed.

End Stabilisers.

Lemma mxsimple_subg : forall M, mxmodule rG M -> mxsimple rH M -> mxsimple rG M.
Proof.
by move=> M modM [_ nzM minM]; split=> // U; move/mxmodule_subg; exact: minM.
Qed.

Lemma subg_mx_irr : mx_irreducible rH -> mx_irreducible rG.
Proof. by apply: mxsimple_subg; exact: mxmodule1. Qed.

Lemma subg_mx_abs_irr :
   mx_absolutely_irreducible rH -> mx_absolutely_irreducible rG.
Proof.
rewrite /mx_absolutely_irreducible -!subset1mx; case/andP=> ->.
move/subsetmx_trans; apply; apply/row_subP=> i.
by rewrite rowK /= envelop_mx_id // (subsetP sHG) ?enum_valP.
Qed.

Lemma rker_subg : rker rH = H :&: rker rG. Proof. exact: rstab_subg. Qed.

Lemma subg_repr_faithful : mx_repr_faithful rG -> mx_repr_faithful rH.
Proof. by apply: subset_trans; rewrite rker_subg subsetIr. Qed.

End SubGroup.

Section SameGroup.

Hypothesis eqGH : G :==: H.

Lemma eqg_repr_proof : H \subset G. Proof. by rewrite (eqP eqGH). Qed.

Definition eqg_repr := subg_repr eqg_repr_proof.
Local Notation rH := eqg_repr.

Lemma rcent_eqg : forall U, rcent rH U = rcent rG U.
Proof. by move=> U; rewrite rcent_subg -(eqP eqGH) (setIidPr _) ?rcent_sub. Qed.

Section Stabilisers.

Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstab_eqg : rstab rH U = rstab rG U.
Proof. by rewrite rstab_subg -(eqP eqGH) (setIidPr _) ?rstab_sub. Qed.

Lemma rstabs_eqg : rstabs rH U = rstabs rG U.
Proof. by rewrite rstabs_subg -(eqP eqGH) (setIidPr _) ?rstabs_sub. Qed.

Lemma mxmodule_eqg : mxmodule rH U = mxmodule rG U.
Proof. by rewrite /mxmodule rstabs_eqg -(eqP eqGH). Qed.

End Stabilisers.

Lemma mxsimple_eqg : forall M, mxsimple rH M <-> mxsimple rG M.
Proof.
move=> M; rewrite /mxsimple mxmodule_eqg.
split=> [] [-> -> minM]; split=> // U modU;
 by apply: minM; rewrite mxmodule_eqg in modU *.
Qed.

Lemma eqg_mx_irr : mx_irreducible rH <-> mx_irreducible rG.
Proof. exact: mxsimple_eqg. Qed.

Lemma eqg_mx_abs_irr :
  mx_absolutely_irreducible rH = mx_absolutely_irreducible rG.
Proof.
by congr (_ && (_ == _)); rewrite /enveloping_algebra_mx /= -(eqP eqGH).
Qed.

Lemma rker_eqg : rker rH = rker rG. Proof. exact: rstab_eqg. Qed.

Lemma eqg_repr_faithful : mx_repr_faithful rH = mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_eqg. Qed.

End SameGroup.

End ChangeGroup.

Section Morphpre.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Variables (G : {group rT}) (n : nat) (rG : mx_representation G n).

Lemma morphpre_mx_repr : mx_repr (f @*^-1 G) (rG \o f).
Proof.
split=> [|x y]; first by rewrite /= morph1 repr_mx1.
case/morphpreP=> Dx Gfx; case/morphpreP=> Dy Gfy.
by rewrite /= morphM ?repr_mxM.
Qed.
Canonical Structure morphpre_repr := MxRepresentation morphpre_mx_repr.
Local Notation rGf := morphpre_repr.

Section Stabilisers.
Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstab_morphpre : rstab rGf U = f @*^-1 (rstab rG U).
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma rstabs_morphpre : rstabs rGf U = f @*^-1 (rstabs rG U).
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma mxmodule_morphpre : G \subset f @* D -> mxmodule rGf U = mxmodule rG U.
Proof. by move=> sGf; rewrite /mxmodule rstabs_morphpre morphpreSK. Qed.

End Stabilisers.

Lemma rker_morphpre : rker rGf = f @*^-1 (rker rG).
Proof. exact: rstab_morphpre. Qed.

Lemma morphpre_mx_irr :
  G \subset f @* D -> (mx_irreducible rGf <-> mx_irreducible rG).
Proof.
move/mxmodule_morphpre=> modG; split; case/mx_irrP=> n_gt0 irrG;
 by apply/mx_irrP; split=> // U modU; apply: irrG; rewrite modG in modU *.
Qed.

Lemma morphpre_mx_abs_irr :
    G \subset f @* D ->
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG.
Proof.
move=> sGfD; congr (_ && (_ == _)); apply/eqP; rewrite mxrank_leqif_sup //.
  apply/row_subP=> i; rewrite rowK.
  case/morphimP: (subsetP sGfD _ (enum_valP i)) => x Dx _ def_i.
  by rewrite def_i (envelop_mx_id rGf) // !inE Dx -def_i enum_valP.
apply/row_subP=> i; rewrite rowK (envelop_mx_id rG) //.
by case/morphpreP: (enum_valP i).
Qed.

End Morphpre.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).
Variables (n : nat) (rGf : mx_representation (f @* G) n).

Definition morphim_mx of G \subset D := fun x => rGf (f x).

Hypothesis sGD : G \subset D.

Lemma morphim_mxE : forall x, morphim_mx sGD x = rGf (f x). Proof. by []. Qed.

Let sG_f'fG : G \subset f @*^-1 (f @* G).
Proof. by rewrite -sub_morphim_pre. Qed.

Lemma morphim_mx_repr : mx_repr G (morphim_mx sGD).
Proof. exact: subg_mx_repr (morphpre_repr f rGf) sG_f'fG. Qed.
Canonical Structure morphim_repr := MxRepresentation morphim_mx_repr.
Local Notation rG := morphim_repr.

Section Stabilisers.
Variables (m : nat) (U : 'M[F]_(m, n)).

Lemma rstab_morphim : rstab rG U = G :&: f @*^-1 rstab rGf U.
Proof. by rewrite -rstab_morphpre -(rstab_subg _ sG_f'fG). Qed.

Lemma rstabs_morphim : rstabs rG U = G :&: f @*^-1 rstabs rGf U.
Proof. by rewrite -rstabs_morphpre -(rstabs_subg _ sG_f'fG). Qed.

Lemma mxmodule_morphim : mxmodule rG U = mxmodule rGf U.
Proof. by rewrite /mxmodule rstabs_morphim subsetI subxx -sub_morphim_pre. Qed.

End Stabilisers.

Lemma rker_morphim : rker rG = G :&: f @*^-1 (rker rGf).
Proof. exact: rstab_morphim. Qed.

Lemma mxsimple_morphim : forall M, mxsimple rG M <-> mxsimple rGf M.
Proof.
move=> M; rewrite /mxsimple mxmodule_morphim.
split=> [] [-> -> minM]; split=> // U modU;
  by apply: minM; rewrite mxmodule_morphim in modU *.
Qed.

Lemma morphim_mx_irr : (mx_irreducible rG <-> mx_irreducible rGf).
Proof. exact: mxsimple_morphim. Qed.

Lemma morphim_mx_abs_irr : 
  mx_absolutely_irreducible rG = mx_absolutely_irreducible rGf.
Proof.
have fG_onto: f @* G \subset restrm sGD f @* G.
  by rewrite morphim_restrm setIid.
rewrite -(morphpre_mx_abs_irr _ fG_onto); congr (_ && (_ == _)).
by rewrite /enveloping_algebra_mx /= morphpre_restrm (setIidPl _).
Qed.

End Morphim.

Section Submodule.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).
Variables (rG : mx_representation G n) (U : 'M[F]_n) (Umod : mxmodule rG U).
Local Notation rU := (submod_repr Umod).
Local Notation rU' := (factmod_repr Umod).

Lemma rfix_submod : (rfix_mx rU G :=: in_submod U (U :&: rfix_mx rG G))%MS.
Proof.
apply/eqmxP; apply/andP; split; last first.
  apply/rfix_mxP=> x Gx; rewrite -in_submodJ ?capmxSl //.
  by rewrite (rfix_mxP G _) ?capmxSr.
rewrite -[rfix_mx _ G]val_submodK subsetmxMr // sub_capmx val_submodP.
by apply/rfix_mxP=> x Gx; rewrite -(val_submodJ Umod) // (rfix_mxP G _).
Qed.

Lemma rfix_factmod : (in_factmod U (rfix_mx rG G) <= rfix_mx rU' G)%MS.
Proof.
by apply/rfix_mxP=> x Gx; rewrite -(in_factmodJ Umod) // (rfix_mxP G _).
Qed.

Lemma rstab_submod : forall m (W : 'M_(m, \rank U)),
  rstab rU W = rstab rG (val_submod W).
Proof.
move=> m W; apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
by rewrite -(inj_eq val_submod_inj) val_submodJ.
Qed.

Lemma rstabs_submod : forall m (W : 'M_(m, \rank U)),
  rstabs rU W = rstabs rG (val_submod W).
Proof.
move=> m W; apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
by rewrite -val_submodS val_submodJ.
Qed.

Lemma val_submod_module : forall m (W : 'M_(m, \rank U)),
   mxmodule rG (val_submod W) = mxmodule rU W.
Proof. by move=> m W; rewrite /mxmodule rstabs_submod. Qed.

Lemma in_submod_module : forall m (V : 'M_(m, n)),
  (V <= U)%MS -> mxmodule rU (in_submod U V) = mxmodule rG V.
Proof. by move=> m V sVU; rewrite -val_submod_module in_submodK. Qed.

Lemma rstab_factmod : forall m (W : 'M_(m, n)),
  rstab rG W \subset rstab rU' (in_factmod U W).
Proof.
move=> m  W; apply/subsetP=> x; case/setIdP=> Gx; move/eqP=> cUW.
by rewrite inE Gx -in_factmodJ //= cUW.
Qed.

Lemma rstabs_factmod : forall m (W : 'M_(m, \rank (cokermx U))),
  rstabs rU' W = rstabs rG (U + val_factmod W)%MS.
Proof.
move=> m W; apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
rewrite addsmxMr addsmx_sub (subsetmx_trans (mxmoduleP Umod x Gx)) ?addsmxSl //.
rewrite -val_factmodS val_factmodJ //= val_factmodS; apply/idP/idP=> nWx.
  rewrite (subsetmx_trans (addsmxSr U _)) // -(in_factmodsK (addsmxSl U _)) //.
  by rewrite addsmxS // val_factmodS in_factmod_addsK.
rewrite in_factmodE (subsetmx_trans (subsetmxMr _ nWx)) // -in_factmodE.
by rewrite in_factmod_addsK val_factmodK.
Qed.

Lemma val_factmod_module : forall m (W : 'M_(m, \rank (cokermx U))),
  mxmodule rG (U + val_factmod W)%MS = mxmodule rU' W.
Proof. by move=> m W; rewrite /mxmodule rstabs_factmod. Qed.

Lemma in_factmod_module : forall m (V : 'M_(m, n)),
  mxmodule rU' (in_factmod U V) = mxmodule rG (U + V)%MS.
Proof.
move=> m V; rewrite -(eqmx_module _ (in_factmodsK (addsmxSl U V))).
by rewrite val_factmod_module (eqmx_module _ (in_factmod_addsK _ _)).
Qed.

Lemma rker_submod : rker rG \subset rker rU.
Proof.
apply/subsetP=> x; case/rkerP=> Gx cVx; rewrite !inE Gx; apply/eqP.
by apply: val_submod_inj; rewrite val_submodJ //= cVx mulmx1.
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

Lemma submod_mx_irr : mx_irreducible rU <-> mxsimple rG U.
Proof.
split=> [] [_ nzU simU].
  rewrite -mxrank_eq0 mxrank1 mxrank_eq0 in nzU; split=> // V [modV sVU] nzV.
  apply/eqmxP; rewrite sVU -(in_submodK sVU) -val_submod1 val_submodS.
  rewrite -(simU <<in_submod U V>>%MS) ?genmxE ?subsetmx1 //=.
    by rewrite (eqmx_module _ (genmxE _)) in_submod_module.
  rewrite -subsetmx0 genmxE -val_submodS in_submodK //.
  by rewrite linear0 eqmx0 subsetmx0.
apply/mx_irrP; rewrite lt0n mxrank_eq0; split=> // V modV.
rewrite -(inj_eq val_submod_inj) linear0 -(eqmx_eq0 (genmxE _)) => nzV.
rewrite -subset1mx -val_submodS val_submod1.
move/simU: nzV => <-; rewrite ?genmxE ?val_submodP //=.
by rewrite (eqmx_module _ (genmxE _)) val_submod_module.
Qed.

End Submodule.

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

Lemma rfix_conj : (rfix_mx rGB G :=: B *m rfix_mx rG G *m invmx B)%MS.
Proof.
apply/eqmxP; apply/andP; split.
  rewrite -mulmxA (eqmxMfull (_ *m _)) ?row_full_unit //.
  rewrite -[rfix_mx rGB G](mulmxK uB) subsetmxMr //; apply/rfix_mxP=> x Gx.
  apply: (canRL (mulmxKV uB)); rewrite -rconj_mxJ mulmxK //.
  by move: x Gx; exact/rfix_mxP.
apply/rfix_mxP=> x Gx; rewrite -3!mulmxA; congr (_ *m _).
by rewrite !mulmxA mulmxKV //; congr (_ *m _); move: x Gx; exact/rfix_mxP.
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

Lemma mxmodule_conj : forall m (U : 'M_(m, n)),
  mxmodule rGB U = mxmodule rG (U *m B).
Proof. by move=> m U; rewrite /mxmodule rstabs_conj. Qed.

Lemma rker_conj : rker rGB = rker rG.
Proof.
apply/setP=> x; rewrite !inE /= mulmxA (can2_eq (mulmxKV uB) (mulmxK uB)).
by rewrite mul1mx -scalar_mxC (inj_eq (can_inj (mulKmx uB))) mul1mx.
Qed.

Lemma conj_repr_faithful : mx_repr_faithful rGB = mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_conj. Qed.

Lemma conj_mx_irr : mx_irreducible rGB <-> mx_irreducible rG.
Proof.
have Bfree: row_free B by rewrite row_free_unit.
split; case/mx_irrP=> n_gt0 irrG; apply/mx_irrP; split=> // U.
  rewrite -[U](mulmxKV uB) -mxmodule_conj -mxrank_eq0 /row_full mxrankMfree //.
  by rewrite mxrank_eq0; exact: irrG.
rewrite -mxrank_eq0 /row_full -(mxrankMfree _ Bfree) mxmodule_conj mxrank_eq0.
exact: irrG.
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

Local Notation E_ r := (enveloping_algebra_mx r).
Lemma quo_mx_quotient : (E_ rGH :=: E_ rG)%MS.
Proof.
apply/eqmxP; apply/andP; split; apply/row_subP=> i.
  rewrite rowK; case/morphimP: (enum_valP i) => x _ Gx ->{i}.
  rewrite quo_repr_coset // (eq_row_sub (enum_rank_in Gx x)) // rowK.
  by rewrite enum_rankK_in.
rewrite rowK -quo_mx_coset ?enum_valP //; set Hx := coset H _.
have GHx: Hx \in (G / H)%g by rewrite mem_quotient ?enum_valP.
by rewrite (eq_row_sub (enum_rank_in GHx Hx)) // rowK enum_rankK_in.
Qed.

Lemma rfix_quo : (rfix_mx rGH (G / H)%g :=: rfix_mx rG G)%MS.
Proof.
apply/eqmxP; apply/andP; (split; apply/rfix_mxP) => [x Gx | Hx].
  by rewrite -quo_mx_coset // (rfix_mxP (G / H)%g _) ?mem_quotient.
by case/morphimP=> x Nx Gx ->; rewrite quo_repr_coset ?(rfix_mxP G _).
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

Lemma mxmodule_quo : forall m (U : 'M_(m, n)), mxmodule rGH U = mxmodule rG U.
Proof.
move=> m U; rewrite /mxmodule rstabs_quo quotientSGK // ?(subset_trans krH) //.
apply/subsetP=> x; rewrite !inE mul1mx; case/andP=> ->; move/eqP->.
by rewrite /= mulmx1.
Qed.

Lemma quo_mx_irr : mx_irreducible rGH <-> mx_irreducible rG.
Proof.
split; case/mx_irrP=> n_gt0 irrG; apply/mx_irrP; split=> // U modU;
  by apply: irrG; rewrite mxmodule_quo in modU *.
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

Section SplittingField.

Implicit Type gT : finGroupType.

Definition group_splitting_field gT (G : {group gT}) :=
  forall n (rG : mx_representation G n),
     mx_irreducible rG -> mx_absolutely_irreducible rG.

Definition group_closure_field gT :=
  forall G : {group gT}, group_splitting_field G.

Lemma quotient_splitting_field : forall gT (G : {group gT}) (H : {set gT}),
  G \subset 'N(H) -> group_splitting_field G -> group_splitting_field (G / H).
Proof.
move=> gT G H nHG splitG n rGH irrGH.
by rewrite -(morphim_mx_abs_irr _ nHG) splitG //; exact/morphim_mx_irr.
Qed.

Lemma coset_splitting_field : forall gT (H : {set gT}),
  group_closure_field gT -> group_closure_field (coset_groupType H).
Proof.
move=> gT H split_gT Gbar; have ->: Gbar = (coset H @*^-1 Gbar / H)%G.
  by apply: val_inj; rewrite /= /quotient morphpreK ?sub_im_coset.
by apply: quotient_splitting_field; [exact: subsetIl | exact: split_gT].
Qed.

End SplittingField.

Section Abelian.

Variables (gT : finGroupType) (G : {group gT}).

Lemma mx_repr_faithful_irr_center_cyclic : forall n rG,
  @mx_repr_faithful _ G n rG -> mx_irreducible rG -> cyclic 'Z(G).
Proof.
case=> [|n] rG injG irrG; first by case/mx_irrP: irrG.
move/trivgP: injG => KrG1; pose rZ := subg_repr rG (center_sub _).
apply: (div_ring_mul_group_cyclic (repr_mx1 rZ)) (repr_mxM rZ) _ _; last first.
  exact: center_abelian.
move=> x; rewrite -[[set _]]KrG1 !inE mul1mx -subr_eq0 andbC; set U := _ - _.
do 2![case/andP]=> Gx cGx; rewrite Gx /=; apply: (mx_Schur irrG).
apply/centgmxP=> y Gy; rewrite mulmx_subl mulmx_subr mulmx1 mul1mx.
by rewrite -!repr_mxM // (centP cGx).
Qed.

Lemma mx_repr_faithful_irr_abelian_cyclic : forall n rG,
  @mx_repr_faithful _ G n rG -> mx_irreducible rG -> abelian G -> cyclic G.
Proof.
move=> n rG injG irrG cGG; rewrite -(setIidPl cGG).
exact: mx_repr_faithful_irr_center_cyclic injG irrG.
Qed.

Hypothesis splitG : group_splitting_field G.

Lemma mx_irr_abelian_linear : forall n rG,
  @mx_irreducible _ G n rG -> abelian G -> n = 1%N.
Proof.
by move=> n rG irrG cGG; apply/eqP; rewrite -(abelian_abs_irr rG) ?splitG.
Qed.

Lemma mxsimple_abelian_linear : forall n rG M,
  abelian G -> @mxsimple _ G n rG M -> \rank M = 1%N.
Proof.
move=> n rG M cGG simM; have [modM _ _] := simM.
by move/(submod_mx_irr modM): simM; move/mx_irr_abelian_linear->.
Qed.

Lemma linear_mxsimple : forall n rG M,
  @mxmodule _ G n rG n M -> \rank M = 1%N -> mxsimple rG M.
Proof.
move=> n rG M modM rM1; apply/(submod_mx_irr modM).
by apply: mx_abs_irrW; rewrite linear_mx_abs_irr.
Qed.

Lemma mxmodule_eigenvector : forall n rG m (M : 'M_(m, n)),
     @mxmodule _ G n rG m M -> \rank M = 1%N ->
  {v : 'rV_n & {a : gT -> F |
     (M :=: v)%MS & {in G, forall x, v *m rG x = a x *m: v}}}.
Proof.
move=> n rG m M modM rM1; set v := nz_row M; exists v.
have defM: (M :=: v)%MS.
  apply/eqmxP; rewrite andbC -(geq_leqif (mxrank_leqif_eq _)) ?nz_row_sub //.
  by rewrite rM1 lt0n mxrank_eq0 nz_row_eq0 -mxrank_eq0 rM1.
pose a x := (v *m rG x *m pinvmx v) 0 0; exists a => // x Gx.
by rewrite -mul_scalar_mx -mx11_scalar mulmxKpV // -defM mxmodule_trans ?defM.
Qed.

End Abelian.

Section AbelianQuotient.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation G n).

Lemma center_kquo_cyclic : mx_irreducible rG -> cyclic 'Z(G / rker rG)%g.
Proof.
move=> irrG; apply: mx_repr_faithful_irr_center_cyclic (kquo_mx_faithful rG) _.
exact/quo_mx_irr.
Qed.

Lemma der1_sub_rker :
    group_splitting_field G -> mx_irreducible rG ->
  (G^`(1) \subset rker rG)%g = (n == 1)%N.
Proof.
move=> splitG irrG; apply/idP/idP; last by move/eqP; exact: rker_linear.
move/sub_der1_abelian; move/(abelian_abs_irr (kquo_repr rG))=> <-.
by apply: (quotient_splitting_field (rker_norm _) splitG); exact/quo_mx_irr.
Qed.

End AbelianQuotient.

Section Similarity.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation reprG := (mx_representation G).

CoInductive mx_rsim n1 (rG1 : reprG n1) n2 (rG2 : reprG n2) : Prop :=
  MxReprSim B of n1 = n2 & row_free B
              & forall x, x \in G -> rG1 x *m B = B *m rG2 x.

Lemma mxrank_rsim : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
  mx_rsim rG1 rG2 -> n1 = n2.
Proof. by move=> n1 n2 rG1 rG2 []. Qed.

Lemma mx_rsim_refl : forall n (rG : reprG n), mx_rsim rG rG.
Proof.
move=> n rG; exists 1%:M => // [|x _]; first by rewrite row_free_unit unitmx1.
by rewrite mulmx1 mul1mx.
Qed.

Lemma mx_rsim_sym : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
  mx_rsim rG1 rG2 ->  mx_rsim rG2 rG1.
Proof.
move=> n1 n2 rG1 rG2 [B def_n1]; rewrite def_n1 in rG1 B *.
rewrite row_free_unit => injB homB; exists (invmx B) => // [|x Gx].
  by rewrite row_free_unit unitmx_inv.
by apply: canRL (mulKmx injB) _; rewrite mulmxA -homB ?mulmxK.
Qed.

Lemma mx_rsim_trans :
  forall n1 n2 n3 (rG1 : reprG n1) (rG2 : reprG n2) (rG3 : reprG n3),
  mx_rsim rG1 rG2 -> mx_rsim rG2 rG3 -> mx_rsim rG1 rG3.
Proof.
move=> n1 n2 n3 rG1 rG2 rG3 [B1 defn1 freeB1 homB1] [B2 defn2 freeB2 homB2].
exists (B1 *m B2); rewrite /row_free ?mxrankMfree 1?defn1 // => x Gx.
by rewrite mulmxA homB1 // -!mulmxA homB2.
Qed.

Lemma mx_rsim_def : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
    mx_rsim rG1 rG2 -> 
  exists B, exists2 B', B' *m B = 1%:M &
    forall x, x \in G -> rG1 x = B *m rG2 x *m B'.
Proof.
move=> n1 n2 rG1 rG2 [B def_n1]; rewrite def_n1 in rG1 B *.
rewrite row_free_unit => injB homB; exists B.
by exists (invmx B) => [|x Gx]; rewrite ?mulVmx // -homB // mulmxK.
Qed.

Lemma mx_rsim_iso : forall n (rG : reprG n) (U V : 'M_n),
    forall (modU : mxmodule rG U) (modV : mxmodule rG V),
  mx_rsim (submod_repr modU) (submod_repr modV) <-> mx_iso rG U V.
Proof.
move=> n rG U V modU modV; split=> [[B eqrUV injB homB] | [f injf homf defV]].
  have: \rank (U *m val_submod (in_submod U 1%:M *m B)) = \rank U.
    do 2!rewrite mulmxA mxrankMfree ?row_base_free //.
    by rewrite -(eqmxMr _ (val_submod1 U)) -in_submodE val_submodK mxrank1.
  case/complete_unitmx => f injf defUf; exists f => //.
    apply/hom_mxP=> x Gx; rewrite -defUf -2!mulmxA -(val_submodJ modV) //.
    rewrite -(mulmxA _ B) -homB // val_submodE 5!mulmxA -in_submodE.
    rewrite -in_submodJ //; have [u ->] := subsetmxP (mxmoduleP modU x Gx).
    by rewrite in_submodE -5!mulmxA (mulmxA _ B) -val_submodE defUf.
  apply/eqmxP; rewrite -mxrank_leqif_eq.
    by rewrite mxrankMfree ?eqrUV ?row_free_unit.
  by rewrite -defUf mulmxA val_submodP.
have eqrUV: \rank U = \rank V by rewrite -defV mxrankMfree ?row_free_unit.
exists (in_submod V (val_submod 1%:M *m f)) => // [|x Gx].
  rewrite /row_free {6}eqrUV -[_ == _]subset1mx -val_submodS.
  rewrite in_submodK; last by rewrite -defV subsetmxMr ?val_submodP.
  by rewrite val_submod1 -defV subsetmxMr ?val_submod1.
rewrite -in_submodJ; last by rewrite -defV subsetmxMr ?val_submodP.
rewrite -(hom_mxP (subsetmx_trans (val_submodP _) homf)) //.
by rewrite -(val_submodJ modU) // mul1mx 2!(mulmxA (_ x)) -val_submodE.
Qed.

Lemma mx_rsim_irr : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
  mx_rsim rG1 rG2 -> mx_irreducible rG1 -> mx_irreducible rG2.
Proof.
move=> n n' rG1 rG2.
case/mx_rsim_sym=> f def_n'; rewrite {n'}def_n' in f rG2 * => injf homf.
case/mx_irrP=> n1_gt0 minG; apply/mx_irrP; split=> // U modU nzU.
rewrite /row_full -(mxrankMfree _ injf) -genmxE.
apply: minG; last by rewrite -mxrank_eq0 genmxE mxrankMfree // mxrank_eq0.
rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
by rewrite -mulmxA -homf // mulmxA subsetmxMr // (mxmoduleP modU).
Qed.

Lemma mx_rsim_abs_irr : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
    mx_rsim rG1 rG2 ->
  mx_absolutely_irreducible rG1 = mx_absolutely_irreducible rG2.
Proof.
move=> n n' rG1 rG2 [f def_n']; rewrite -{n'}def_n' in f rG2 *.
rewrite row_free_unit => injf homf; congr (_ && (_ == _)).
pose Eg (g : 'M[F]_n) := lin_mx (mulmxr (invmx g) \o mulmx g).
have free_Ef: row_free (Eg f).
  apply/row_freeP; exists (Eg (invmx f)).
  apply/row_matrixP=> i; rewrite rowE row1 mulmxA mul_rV_lin mx_rV_lin /=.
  by rewrite invmxK !{1}mulmxA mulmxKV // -mulmxA mulKmx // vec_mxK.
symmetry; rewrite -(mxrankMfree _ free_Ef); congr (\rank _).
apply/row_matrixP=> i; rewrite row_mul !rowK mul_vec_lin /=.
by rewrite -homf ?enum_valP // mulmxK.
Qed.

Lemma rker_mx_rsim : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
  mx_rsim rG1 rG2 -> rker rG1 = rker rG2.
Proof.
move=> n n' rG1 rG2 [f def_n']; rewrite -{n'}def_n' in f rG2 *.
rewrite row_free_unit => injf homf.
apply/setP=> x; rewrite !inE !mul1mx; apply: andb_id2l => Gx.
by rewrite -(can_eq (mulmxK injf)) homf // -scalar_mxC (can_eq (mulKmx injf)).
Qed.

Lemma mx_rsim_faithful : forall n1 n2 (rG1 : reprG n1) (rG2 : reprG n2),
  mx_rsim rG1 rG2 -> mx_repr_faithful rG1 = mx_repr_faithful rG2.
Proof.
by move=> n1 n2 rG1 rG2 simG12; rewrite /mx_repr_faithful (rker_mx_rsim simG12).
Qed.

End Similarity.

Section Socle.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation G n) (sG : socleType rG).

Lemma socle_irr : forall W : sG, mx_irreducible (socle_repr W).
Proof. move=> W; apply/submod_mx_irr; exact: socle_simple. Qed.

Lemma socle_rsimP : forall W1 W2 : sG,
  reflect (mx_rsim (socle_repr W1) (socle_repr W2)) (W1 == W2).
Proof.
move=> W1 W2; have [simW1 simW2] := (socle_simple W1, socle_simple W2).
by apply: (iffP (component_mx_isoP simW1 simW2)); move/mx_rsim_iso; exact.
Qed.

End Socle.

Section Clifford.

Variables (gT : finGroupType) (G H : {group gT}).
Hypothesis nsHG : H <| G.
Variables (n : nat) (rG : mx_representation G n).
Let sHG := normal_sub nsHG.
Let nHG := normal_norm nsHG.
Let rH := subg_repr rG sHG.

Lemma Clifford_simple : forall M x,
  mxsimple rH M -> x \in G -> mxsimple rH (M *m rG x).
Proof.
have modmG: forall U x, x \in G -> mxmodule rH U -> mxmodule rH (U *m rG x).
  move=> m U x Gx modU; apply/mxmoduleP=> h Hh; have Gh := subsetP sHG h Hh.
  rewrite -mulmxA -repr_mxM // conjgCV repr_mxM ?groupJ ?groupV // mulmxA.
  by rewrite subsetmxMr ?(mxmoduleP modU) // -mem_conjg (normsP nHG).
have nzmG: forall x U, x \in G -> (U *m rG x == 0) = (U == 0).
  by move=> m x U Gx; rewrite -{1}(mul0mx m (rG x)) (can_eq (repr_mxK rG Gx)).
move=> M x [modM nzM simM] Gx; have Gx' := groupVr Gx.
split=> [||U [modU sUMx] nzU]; rewrite ?modmG ?nzmG //; apply/eqmxP.
rewrite sUMx -(repr_mxKV rG Gx U) subsetmxMr //.
by rewrite (simM (U *m _)) ?modmG ?nzmG // -(repr_mxK rG Gx M) subsetmxMr.
Qed.

Lemma Clifford_hom : forall x m (U : 'M_(m, n)),
  x \in 'C_G(H) -> (U <= dom_hom_mx rH (rG x))%MS.
Proof.
move=> x m U; case/setIP=> Gx cHx; apply/rV_subP=> v _{U}.
apply/hom_mxP=> h Hh; have Gh := subsetP sHG h Hh.
by rewrite -!mulmxA /= -!repr_mxM // (centP cHx).
Qed.

Lemma Clifford_iso : forall x U, x \in 'C_G(H) -> mx_iso rH U (U *m rG x).
Proof.
move=> x M cHx; have [Gx _] := setIP cHx.
by exists (rG x); rewrite ?repr_mx_unit ?Clifford_hom.
Qed.

Lemma Clifford_iso2 : forall x U V,
  mx_iso rH U V -> x \in G -> mx_iso rH (U *m rG x) (V *m rG x).
Proof.
move=> x U V [f injf homUf defV] Gx; have Gx' := groupVr Gx.
pose fx := rG (x^-1)%g *m f *m rG x; exists fx; last 1 first.
- by rewrite !mulmxA repr_mxK //; exact: eqmxMr.
- by rewrite !unitmx_mul andbC !repr_mx_unit.
apply/hom_mxP=> h Hh; have Gh := subsetP sHG h Hh.
rewrite -(mulmxA U) -repr_mxM // conjgCV repr_mxM ?groupJ // !mulmxA.
rewrite !repr_mxK // (hom_mxP homUf) -?mem_conjg ?(normsP nHG) //=.
by rewrite !repr_mxM ?invgK ?groupM // !mulmxA repr_mxKV.
Qed.

Lemma Clifford_componentJ : forall M x,
    mxsimple rH M -> x \in G ->
  (component_mx rH (M *m rG x) :=: component_mx rH M *m rG x)%MS.
Proof.
set simH := mxsimple rH; set cH := component_mx rH.
have actG: {in G, forall x M, simH M -> cH M *m rG x <= cH (M *m rG x)}%MS.
  move=> x Gx /= M simM; have [I [U isoU def_cHM]] := component_mx_def simM.
  rewrite /cH def_cHM sumsmxMr; apply/sumsmx_subP=> i _.
  by apply: mx_iso_component; [exact: Clifford_simple | exact: Clifford_iso2].
move=> M x simM Gx; apply/eqmxP; rewrite actG // -/cH.
rewrite -{1}[cH _](repr_mxKV rG Gx) subsetmxMr // -{2}[M](repr_mxK rG Gx).
by rewrite actG ?groupV //; exact: Clifford_simple.
Qed.

Hypothesis irrG : mx_irreducible rG.

Lemma Clifford_basis : forall M, mxsimple rH M ->
  {X : {set gT} | X \subset G &
    let S := \sum_(x \in X) M *m rG x in S :=: 1%:M /\ mxdirect S}%MS.
Proof.
move=> M simM.
have simMG: forall g : subg_of G, mxsimple rH (M *m rG (val g)).
  by case=> x Gx; exact: Clifford_simple.
have [|XG [defX1 dxX1]] := sum_mxsimple_direct_sub simMG (_ : _ :=: 1%:M)%MS.
  case irrG => _ _; apply; rewrite ?subsetmx1 //; last first.
    rewrite -subsetmx0; apply/sumsmx_subP; move/(_ 1%g (erefl _)); apply: negP.
    by rewrite subsetmx0 repr_mx1 mulmx1; case simM.
  apply/mxmoduleP=> x Gx; rewrite sumsmxMr; apply/sumsmx_subP=> [[y Gy]] /= _.
  by rewrite (sumsmx_sup (subg G (y * x))) // subgK ?groupM // -mulmxA repr_mxM.
exists (val @: XG); first by apply/subsetP=> ?; case/imsetP=> [[x Gx]] _ ->.
have bij_val: {on val @: XG, bijective (@sgval _ G)}.
  exists (subg G) => [g _ | x]; first exact: sgvalK.
  by case/imsetP=> [[x' Gx]] _ ->; rewrite subgK.
have defXG: forall g, (val g \in val @: XG) = (g \in XG).
  by move=> g; apply/imsetP/idP=> [[h XGh] | XGg]; [move/val_inj-> | exists g].
by rewrite /= mxdirectE /= !(reindex _ bij_val) !(eq_bigl _ _ defXG).
Qed.

Variable sH : socleType rH.

Definition Clifford_act (W : sH) x :=
  let Gx := subgP (subg G x) in
  PackSocle (component_socle sH (Clifford_simple (socle_simple W) Gx)).

Let valWact : forall W x, (Clifford_act W x :=: W *m rG (sgval (subg G x)))%MS.
Proof.
move=> W x0; rewrite PackSocleK; apply: Clifford_componentJ (subgP _).
exact: socle_simple.
Qed.

Fact Clifford_is_action : is_action G Clifford_act.
Proof.
split=> [x W W' eqWW' | W x y Gx Gy].
  pose Gx := subgP (subg G x); apply/socleP; apply/eqmxP.
  rewrite -(repr_mxK rG Gx W) -(repr_mxK rG Gx W'); apply: eqmxMr.
  apply: eqmx_trans (eqmx_sym _) (valWact _ _); rewrite -eqWW'; exact: valWact.
apply/socleP; rewrite !{1}valWact 2!{1}(eqmxMr _ (valWact _ _)).
by rewrite !subgK ?groupM ?repr_mxM ?mulmxA ?andbb.
Qed.

Definition Clifford_action := Action Clifford_is_action.

Local Notation "'Cl" := Clifford_action (at level 0) : action_scope.

Lemma val_Clifford_act : forall W x, x \in G -> ('Cl%act W x :=: W *m rG x)%MS.
Proof. by move=> W x Gx; apply: eqmx_trans (valWact _ _) _; rewrite subgK. Qed.

Lemma Clifford_atrans : [transitive G, on [set: sH] | 'Cl].
Proof.
have [_ nz1 _] := irrG.
apply: mxsimple_exists (mxmodule1 rH) nz1 _ _ => [[M simM _]].
pose W1 := PackSocle (component_socle sH simM).
have [X sXG [def1 _]] := Clifford_basis simM; move/subsetP: sXG => sXG.
apply/imsetP; exists W1; first by rewrite inE.
symmetry; apply/setP=> W; rewrite inE; have simW := socle_simple W.
have:= subsetmx1 (socle_base W); rewrite -def1 -[(\sum_(x \in X) _)%MS]mulmx1.
case/(hom_mxsemisimple_iso simW) => [x Xx _ | | x Xx isoMxW].
- by apply: Clifford_simple; rewrite ?sXG.
- exact: scalar_mx_hom.
have Gx := sXG x Xx; apply/imsetP; exists x => //.
apply/socleP; apply/eqmxP; apply: eqmx_sym.
apply: eqmx_trans (val_Clifford_act _ Gx) _; rewrite PackSocleK.
apply: eqmx_trans (eqmx_sym (Clifford_componentJ simM Gx)) _.
apply/eqmxP; rewrite (sameP genmxP eqP) !{1}genmx_component.
by apply/component_mx_isoP=> //; exact: Clifford_simple.
Qed.

Lemma Clifford_Socle1 : Socle sH = 1%:M.
Proof.
case/imsetP: Clifford_atrans => W _ _; have simW := socle_simple W.
have [X sXG [def1 _]] := Clifford_basis simW.
rewrite reducible_Socle1 //; apply: mxsemisimple_reducible.
apply: intro_mxsemisimple def1 _ => x; move/(subsetP sXG)=> Gx _.
exact: Clifford_simple.
Qed.

Lemma Clifford_rank_components : forall W : sH, (#|sH| * \rank W)%N = n.
Proof.
move=> W; rewrite -{9}(mxrank1 F n) -Clifford_Socle1.
rewrite (mxdirectP (Socle_direct sH)) /= -sum_nat_const.
apply: eq_bigr => W1 _; have [W0 _ W0G] := imsetP Clifford_atrans.
have{W0G} W0G: _ \in orbit 'Cl G W0 by move=> W'; rewrite -W0G inE.
case/orbitP: (W0G W) => x Gx <-; case/orbitP: (W0G W1) => y Gy <-.
by rewrite !{1}val_Clifford_act // !mxrankMfree // !repr_mx_free.
Qed.

Theorem Clifford_component_basis : forall M, mxsimple rH M ->
  {t : nat & {x_ : sH -> 'I_t -> gT |
    forall W, let sW := (\sum_j M *m rG (x_ W j))%MS in
      [/\ forall j, x_ W j \in G, (sW :=: W)%MS & mxdirect sW]}}.
Proof.
move=> M simM; pose t := (n %/ #|sH| %/ \rank M)%N; exists t.
have [X sXG [defX1 dxX1]] := Clifford_basis simM; move/subsetP: sXG => sXG.
pose sMv (W : sH) x := (M *m rG x <= W)%MS; pose Xv := [pred x \in X | sMv _ x].
have sXvG: {subset Xv _ <= G} by move=> W x; case/andP; move/sXG.
have defW: forall W, (\sum_(x \in Xv W) M *m rG x :=: W)%MS.
  move=> W; apply/eqmxP; rewrite -(geq_leqif (mxrank_leqif_eq _)); last first.
    by apply/sumsmx_subP=> x; case/andP.
  rewrite -(leq_add2r (\sum_(W' | W' != W) \rank W')) -((bigD1 W) predT) //=.
  rewrite -(mxdirectP (Socle_direct sH)) /= -/(Socle _) Clifford_Socle1 -defX1.
  apply: leq_trans (mxrankS _) (mxrank_sum_leqif _).1 => /=.
  rewrite (bigID (sMv W))%MS addsmxS //=.
  apply/sumsmx_subP=> x; case/andP=> Xx notW_Mx; have Gx := sXG x Xx.
  have simMx := Clifford_simple simM Gx.
  pose Wx := PackSocle (component_socle sH simMx).
  have sMxWx: (M *m rG x <= Wx)%MS by rewrite PackSocleK component_mx_id.
  by rewrite (sumsmx_sup Wx) //; apply: contra notW_Mx; move/eqP=> <-.
have dxXv: mxdirect (\sum_(x \in Xv _) M *m rG x).
  move=> W; move: dxX1; rewrite !mxdirectE /= !(bigID (sMv W) (mem X)) /=.
  by rewrite -mxdirectE mxdirect_addsE /=; case/andP.
have def_t: #|Xv _| = t.
  move=> W; rewrite /t -{1}(Clifford_rank_components W) mulKn 1?(cardD1 W) //.
  rewrite -defW (mxdirectP (dxXv W)) /= (eq_bigr (fun _ => \rank M)) => [|x].
    rewrite sum_nat_const mulnK //; last by rewrite lt0n mxrank_eq0; case simM.
  by move/sXvG=> Gx; rewrite mxrankMfree // row_free_unit repr_mx_unit.
exists (fun W i => enum_val (cast_ord (esym (def_t W)) i)) => W.
case: {def_t}t / (def_t W) => sW.
case: (pickP (Xv W)) => [x0 XvWx0 | XvW0]; last first.
  by case/negP: (nz_socle W); rewrite -subsetmx0 -defW big_pred0.
have{x0 XvWx0} reXv := reindex _ (enum_val_bij_in XvWx0).
have def_sW: (sW :=: W)%MS.
  apply: eqmx_trans (defW W); apply/eqmxP; apply/genmxP; congr <<_>>%MS.
  rewrite reXv /=; apply: eq_big => [j | j _]; first by move: (enum_valP j).
  by rewrite cast_ord_id.
split=> // [j|]; first by rewrite (sXvG W) ?enum_valP.
apply/mxdirectP; rewrite def_sW -(defW W) /= (mxdirectP (dxXv W)) /= reXv /=.
by apply: eq_big => [j | j _]; [move: (enum_valP j) | rewrite cast_ord_id].
Qed.

Lemma Clifford_astab : H <*> 'C_G(H) \subset 'C([set: sH] | 'Cl).
Proof.
rewrite mulgen_subG !subsetI sHG subsetIl /=; apply/andP; split.
  apply/subsetP=> h Hh; have Gh := subsetP sHG h Hh; rewrite inE.
  apply/subsetP=> W _; have simW := socle_simple W; have [modW _ _] := simW.
  have simWh: mxsimple rH (socle_base W *m rG h) by exact: Clifford_simple.
  rewrite inE -val_eqE /= PackSocleK eq_sym.
  apply/component_mx_isoP; rewrite ?subgK //; apply: component_mx_iso => //.
  by apply: subsetmx_trans (component_mx_id simW); move/mxmoduleP: modW => ->.
apply/subsetP=> z cHz; have [Gz _] := setIP cHz; rewrite inE.
apply/subsetP=> W _; have simW := socle_simple W; have [modW _ _] := simW.
have simWz: mxsimple rH (socle_base W *m rG z) by exact: Clifford_simple.
rewrite inE -val_eqE /= PackSocleK eq_sym.
by apply/component_mx_isoP; rewrite ?subgK //; exact: Clifford_iso.
Qed.

Lemma Clifford_astab1 : forall W : sH, 'C[W | 'Cl] = rstabs rG W. 
Proof.
move=> W; apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
rewrite sub1set inE (sameP eqP socleP) !val_Clifford_act //.
rewrite andb_idr // => sWxW; rewrite -mxrank_leqif_sup //.
by rewrite mxrankMfree ?repr_mx_free.
Qed.

Lemma Clifford_rstabs_simple : forall W : sH,
  mxsimple (subg_repr rG (rstabs_sub rG W)) W.
Proof.
move=> W; split => [||U modU sUW nzU]; last 2 [exact: nz_socle].
  by rewrite /mxmodule rstabs_subg setIid.
apply/eqmxP; rewrite sUW /=.
have modUH: mxmodule rH U.
  apply/mxmoduleP=> h Hh; rewrite (mxmoduleP modU) //.
  rewrite /= -Clifford_astab1 !(inE, sub1set) (subsetP sHG) //.
  rewrite (astab_act (subsetP Clifford_astab h _)) ?inE //=.
  by rewrite mem_gen // inE Hh.
apply: (mxsimple_exists modUH nzU) => [[M simM sMU]].
have [t [x_]] := Clifford_component_basis simM; case/(_ W) => Gx_ defW _.
rewrite -defW; apply/sumsmx_subP=> j _; set x := x_ W j.
have{Gx_} Gx: x \in G by rewrite Gx_.
apply: subsetmx_trans (subsetmxMr _ sMU) _; apply: (mxmoduleP modU).
rewrite inE -val_Clifford_act Gx //; set Wx := 'Cl%act W x.
case: (eqVneq Wx W) => [-> //= | neWxW ].
case: (simM) => _; case/negP; rewrite -subsetmx0.
rewrite (canF_eq (actKin 'Cl Gx)) in neWxW.
rewrite -(component_mx_disjoint _ _ neWxW); try exact: socle_simple.
rewrite sub_capmx {1}(subsetmx_trans sMU sUW) val_Clifford_act ?groupV //.
by rewrite -(eqmxMr _ defW) sumsmxMr (sumsmx_sup j) ?repr_mxK.
Qed.

End Clifford.

Section JordanHolder.

Variables (gT : finGroupType) (G : {group gT}).
Variables (n : nat) (rG : mx_representation G n).
Local Notation modG := ((mxmodule rG) n).

Lemma subfact_module : forall (U V : 'M_n) (modU : modG U),
  modG V -> mxmodule (factmod_repr modU) <<in_factmod U V>>%MS.
Proof.
move=> U V modU modV; rewrite (eqmx_module _ (genmxE _)) in_factmod_module.
by rewrite addsmx_module.
Qed.

Definition subfact_repr U V (modU : modG U) (modV : modG V) :=
  submod_repr (subfact_module modU modV).

Lemma mx_factmod_sub : forall U modU,
  mx_rsim (@subfact_repr U _ modU (mxmodule1 rG)) (factmod_repr modU).
Proof.
move=> U modU; exists (val_submod 1%:M) => [||x Gx].
- apply: (@addIn (\rank U)); rewrite genmxE mxrank_in_factmod mxrank_coker.
  by rewrite (addsmx_idPr (subsetmx1 U)) mxrank1 subnK ?rank_leq_row.
- by rewrite /row_free val_submod1.
by rewrite -[_ x]mul1mx -val_submodE val_submodJ.
Qed.

Definition max_submod (U V : 'M_n) :=
  (U < V)%MS /\ (forall W, ~ [/\ modG W, U < W & W < V])%MS.

Lemma max_submodP : forall U V (modU : modG U) (modV : modG V),
  (U <= V)%MS -> (max_submod U V <-> mx_irreducible (subfact_repr modU modV)).
Proof.
move=> U V modU modV sUV; split=> [[ltUV maxU] | ].
  apply/mx_irrP; split=> [|WU modWU nzWU].
    by rewrite genmxE lt0n mxrank_eq0 in_factmod_eq0; case/andP: ltUV.
  rewrite -subset1mx -val_submodS val_submod1 genmxE.
  pose W := (U + val_factmod (val_submod WU))%MS.
  suffices sVW: (V <= W)%MS.
    rewrite {2}in_factmodE (subsetmx_trans (subsetmxMr _ sVW)) //.
    rewrite addsmxMr -!in_factmodE val_factmodK.
    by rewrite ((in_factmod U U =P 0) _) ?adds0mx ?in_factmod_eq0.
  move/and3P: {maxU}(maxU W); apply: contraR; rewrite /ltmx addsmxSl => -> /=.
  move: modWU; rewrite /mxmodule rstabs_submod rstabs_factmod => -> /=.
  rewrite addsmx_sub subsetmx_refl -in_factmod_eq0 val_factmodK.
  move: nzWU; rewrite -[_ == 0](inj_eq val_submod_inj) linear0 => ->.
  rewrite -(in_factmodsK sUV) addsmxS // val_factmodS.
  by rewrite -(genmxE (in_factmod U V)) val_submodP.
case/mx_irrP; rewrite lt0n {1}genmxE mxrank_eq0 in_factmod_eq0 => ltUV maxV.
split=> // [|W [modW]]; first exact/andP.
case/andP=> sUW ltUW; case/andP=> sWV; case/negP.
rewrite -(in_factmodsK sUV) -(in_factmodsK sUW) addsmxS // val_factmodS.
rewrite -genmxE -val_submod1; set VU := <<_>>%MS.
have sW_VU: (in_factmod U W <= VU)%MS.
  by rewrite genmxE -val_factmodS !subsetmxMr.
rewrite -(in_submodK sW_VU) val_submodS -(genmxE (in_submod _ _)).
rewrite subset1mx maxV //.
  rewrite (eqmx_module _ (genmxE _)) in_submod_module ?genmxE ?subsetmxMr //.
  by rewrite in_factmod_module addsmx_module.
rewrite -subsetmx0 [(_ <= 0)%MS]genmxE -val_submodS linear0 in_submodK //.
by rewrite eqmx0 subsetmx0 in_factmod_eq0.
Qed.

Lemma max_submod_eqmx : forall U1 U2 V1 V2,
  (U1 :=: U2)%MS -> (V1 :=: V2)%MS -> max_submod U1 V1 -> max_submod U2 V2.
Proof.
move=> U1 U2 V1 V2 eqU12 eqV12 [ltUV1 maxU1].
by split=> [|W]; rewrite -(lt_eqmx eqU12) -(lt_eqmx eqV12).
Qed.

Definition mx_subseries := all modG.

Definition mx_composition_series V :=
  mx_subseries V /\ (forall i, i < size V -> max_submod (0 :: V)`_i V`_i).
Local Notation mx_series := mx_composition_series.

Fact mx_subseries_module : forall V i, mx_subseries V -> mxmodule rG V`_i.
Proof.
move=> V i modV; case: (leqP (size V) i) => [leVi |]; last exact: all_nthP.
by rewrite nth_default ?mxmodule0.
Qed.

Fact mx_subseries_module' : forall V i,
   mx_subseries V -> mxmodule rG (0 :: V)`_i.
Proof. by move=> V i modV; rewrite mx_subseries_module //= mxmodule0. Qed.

Definition subseries_repr V i (modV : all modG V) :=
  subfact_repr (mx_subseries_module' i modV) (mx_subseries_module i modV).

Definition series_repr V i (compV : mx_composition_series V) :=
  subseries_repr i (proj1 compV).

Lemma mx_series_lt : forall V, mx_composition_series V -> path ltmx 0 V.
Proof. by move=> V [_ compV]; apply/(pathP 0)=> i; case/compV. Qed.

Lemma max_size_mx_series : forall V : seq 'M[F]_n,
   path ltmx 0 V -> size V <= \rank (last 0 V).
Proof.
move=> V; rewrite -[size V]addn0 -(mxrank0 F n n); elim: V 0 => //= V1 V IHV V0.
rewrite ltmxErank -andbA; case/and3P=> _ ltV01 ltV.
by apply: leq_trans (IHV _ ltV); rewrite addSnnS leq_add2l.
Qed.

Lemma mx_series_repr_irr : forall V i (compV : mx_composition_series V),
  i < size V -> mx_irreducible (series_repr i compV).
Proof.
move=> V i [modV compV]; move/compV=> maxVi; apply/max_submodP => //.
by apply: ltmxW; case: maxVi.
Qed.

Lemma mx_series_rcons : forall U V,
  mx_series (rcons U V) <-> [/\ mx_series U, modG V & max_submod (last 0 U) V].
Proof.
move=> U V; rewrite /mx_series /mx_subseries all_rcons size_rcons -rcons_cons.
split=> [ [] | [[modU maxU] modV maxV]].
  case/andP=> modU modV maxU; split=> //; last first.
    by have:= maxU _ (leqnn _); rewrite !nth_rcons leqnn ltnn eqxx -last_nth.
  by split=> // i ltiU; have:= maxU i (ltnW ltiU); rewrite !nth_rcons leqW ltiU.
rewrite modV; split=> // i; rewrite !nth_rcons ltnS leq_eqVlt.
case: eqP => [-> _ | /= _ ltiU]; first by rewrite ltnn eqxx -last_nth.
by rewrite ltiU; exact: maxU.
Qed.

Theorem mx_Schreier : forall U,
    mx_subseries U -> path ltmx 0 U ->
  classically (exists V, [/\ mx_series V, last 0 V :=: 1%:M & subseq U V])%MS.
Proof.
move=> U0; set U := {1 2}U0; have: subseq U0 U := subseq_refl U.
pose n' := n.+1; have: n < size U + n' by rewrite leq_addl.
elim: n' U => [|n' IH_U] U ltUn' sU0U modU incU [] // noV.
  rewrite addn0 ltnNge in ltUn'; case/negP: ltUn'.
  by rewrite (leq_trans (max_size_mx_series incU)) ?rank_leq_row.
apply noV; exists U; split => //; first split=> // i lt_iU; last first.
  apply/eqmxP; apply: contraT => neU1.
  apply: {IH_U}(IH_U (rcons U 1%:M)) noV.
  - by rewrite size_rcons addSnnS.
  - by rewrite (subseq_trans sU0U) ?subseq_rcons.
  - by rewrite /mx_subseries all_rcons mxmodule1.
  by rewrite path_rcons ltmxEneq neU1 subsetmx1 !andbT.
set U'i := _`_i; set Ui := _`_i; have defU := cat_take_drop i U.
have defU'i: U'i = last 0 (take i U).
  rewrite (last_nth 0) /U'i -{1}defU -cat_cons nth_cat /=.
  by rewrite size_take lt_iU leqnn.
move: incU; rewrite -defU path_cat (drop_nth 0) //= -/Ui -defU'i.
set U' := take i U; set U'' := drop _ U; case/and3P=> incU' ltUi incU''.
split=> // W [modW ltUW ltWV]; case: not_false.
apply: {IH_U}(IH_U (U' ++ W :: Ui :: U'')) noV; last 2 first.
- by rewrite /mx_subseries -drop_nth // all_cat /= modW -all_cat defU.
- by rewrite path_cat /= -defU'i; exact/and4P.
- by rewrite -drop_nth // size_cat /= addnS -size_cat defU addSnnS.
by rewrite (subseq_trans sU0U) // -defU subseq_cat // -drop_nth ?subseq_cons.
Qed.

Lemma mx_second_rsim : forall U V (modU : modG U) (modV : modG V),
  let modI := capmx_module modU modV in let modA := addsmx_module modU modV in
  mx_rsim (subfact_repr modI modU) (subfact_repr modV modA).
Proof.
move=> U V modU modV modI modA; set nI := {1}(\rank _).
have sIU := capmxSl U V; have sVA := addsmxSr U V.
pose valI := val_factmod (val_submod (1%:M : 'M_nI)).
have UvalI: (valI <= U)%MS.
  rewrite -(addsmx_idPr sIU) (subsetmx_trans _ (proj_factmodS _ _)) //.
  by rewrite subsetmxMr // val_submod1 genmxE.
exists (valI *m in_factmod _ 1%:M *m in_submod _ 1%:M) => [||x Gx].
- apply: (@addIn (\rank (U :&: V) + \rank V)%N); rewrite genmxE addnA addnCA.
  rewrite /nI genmxE !{1}mxrank_in_factmod 2?(addsmx_idPr _) //.
  by rewrite -mxrank_sum_cap addnC. 
- rewrite -kermx_eq0; apply/rowV0P=> u; rewrite (sameP sub_kermxP eqP).
  rewrite mulmxA -in_submodE mulmxA -in_factmodE -(inj_eq val_submod_inj).
  rewrite linear0 in_submodK ?in_factmod_eq0 => [Vvu|]; last first.
    by rewrite genmxE addsmxC in_factmod_addsK subsetmxMr // mulmx_sub.
  apply: val_submod_inj; apply/eqP; rewrite linear0 -[val_submod u]val_factmodK.
  rewrite val_submodE val_factmodE -mulmxA -val_factmodE -/valI.
  by rewrite in_factmod_eq0 sub_capmx mulmx_sub.
symmetry; rewrite -{1}in_submodE -{1}in_submodJ; last first.
  by rewrite genmxE addsmxC in_factmod_addsK -in_factmodE subsetmxMr.
rewrite -{1}in_factmodE -{1}in_factmodJ // mulmxA in_submodE; congr (_ *m _).
apply/eqP; rewrite mulmxA -in_factmodE -subr_eq0 -linear_sub in_factmod_eq0.
apply: subsetmx_trans (capmxSr U V); rewrite -in_factmod_eq0 linear_sub /=.
rewrite subr_eq0 {1}(in_factmodJ modI) // val_factmodK eq_sym.
rewrite /valI val_factmodE mulmxA -val_factmodE val_factmodK.
by rewrite -[submod_mx _ _]mul1mx -val_submodE val_submodJ.
Qed.

Lemma subfact_eqmx_add : forall U1 U2 V1 V2 modU1 modU2 modV1 modV2,
    (U1 :=: U2)%MS -> (U1 + V1 :=: U2 + V2)%MS ->
  mx_rsim (@subfact_repr U1 V1 modU1 modV1) (@subfact_repr U2 V2 modU2 modV2).
Proof.
move=> U1 U2 V1 V2 modU1 modU2 modV1 modV2 eqU12 eqV12.
set n1 := {1}(\rank _); pose v1 := val_factmod (val_submod (1%:M : 'M_n1)).
have sv12: (v1 <= U2 + V2)%MS.
  rewrite -eqV12 (subsetmx_trans _ (proj_factmodS _ _)) //.
  by rewrite subsetmxMr // val_submod1 genmxE.
exists (v1 *m in_factmod _ 1%:M *m in_submod _ 1%:M) => [||x Gx].
- apply: (@addIn (\rank U1)); rewrite {2}eqU12 /n1 !{1}genmxE.
  by rewrite !{1}mxrank_in_factmod eqV12.
- rewrite -kermx_eq0; apply/rowV0P=> u; rewrite (sameP sub_kermxP eqP) mulmxA.
  rewrite -in_submodE mulmxA -in_factmodE -(inj_eq val_submod_inj) linear0.
  rewrite in_submodK ?in_factmod_eq0 -?eqU12 => [U1uv1|]; last first.
    by rewrite genmxE -(in_factmod_addsK U2 V2) subsetmxMr // mulmx_sub.
  apply: val_submod_inj; apply/eqP; rewrite linear0 -[val_submod _]val_factmodK.
  by rewrite in_factmod_eq0 val_factmodE val_submodE -mulmxA -val_factmodE.
symmetry; rewrite -{1}in_submodE -{1}in_factmodE -{1}in_submodJ; last first.
  by rewrite genmxE -(in_factmod_addsK U2 V2) subsetmxMr.
rewrite -{1}in_factmodJ // mulmxA in_submodE; congr (_ *m _); apply/eqP.
rewrite mulmxA -in_factmodE -subr_eq0 -linear_sub in_factmod_eq0 -eqU12.
rewrite -in_factmod_eq0 linear_sub /= subr_eq0 {1}(in_factmodJ modU1) //.
rewrite val_factmodK /v1 val_factmodE eq_sym mulmxA -val_factmodE val_factmodK.
by rewrite -[_ *m _]mul1mx mulmxA -val_submodE val_submodJ.
Qed.

Lemma subfact_eqmx : forall U1 U2 V1 V2 modU1 modU2 modV1 modV2,
    forall (eqU : (U1 :=: U2)%MS) (eqV : (V1 :=: V2)%MS), 
  mx_rsim (@subfact_repr U1 V1 modU1 modV1) (@subfact_repr U2 V2 modU2 modV2).
Proof. by move=> *; apply: subfact_eqmx_add => //; exact: adds_eqmx. Qed.

Lemma mx_butterfly : forall U V W modU modV modW,
    ~~ (U == V)%MS -> max_submod U W -> max_submod V W ->
  let modUV := capmx_module modU modV in 
     max_submod (U :&: V)%MS U
  /\ mx_rsim (@subfact_repr V W modV modW) (@subfact_repr _ U modUV modU).
Proof.
move=> U V W modU modV modW neUV maxU maxV modUV.
have{neUV maxU} defW: (U + V :=: W)%MS.
  wlog{neUV modUV} ltUV: U V modU modV maxU maxV / ~~ (V <= U)%MS.
    by case/nandP: neUV => ?; first rewrite addsmxC; exact.
  apply/eqmxP; apply/idPn=> neUVW; case: maxU => ltUW; case/(_ (U + V)%MS).
  rewrite addsmx_module // ltmxE ltmxEneq neUVW addsmxSl !addsmx_sub.
  by have [ltVW _] := maxV; rewrite subsetmx_refl andbT ltUV !ltmxW.
have sUV_U := capmxSl U V; have sVW: (V <= W)%MS by rewrite -defW addsmxSr.
set goal := mx_rsim _ _; suffices{maxV} simUV: goal.
  split=> //; apply/(max_submodP modUV modU sUV_U).
  by apply: mx_rsim_irr simUV _; exact/max_submodP.
apply: {goal}mx_rsim_sym.
by apply: mx_rsim_trans (mx_second_rsim modU modV) _; exact: subfact_eqmx.
Qed.

Lemma mx_JordanHolder_exists : forall U V,
    mx_composition_series U -> modG V -> max_submod V (last 0 U) ->
  {W : seq 'M_n | mx_composition_series W & last 0 W = V}.
Proof.
elim/last_ind=> [|U Um IHU] V compU modV; first by case; rewrite ltmx0.
rewrite last_rcons => maxV; case/mx_series_rcons: compU => compU modUm maxUm.
case eqUV: (last 0 U == V)%MS.
  case/lastP: U eqUV compU {maxUm IHU} => [|U' Um'].
    by rewrite andbC; move/eqmx0P->; exists [::].
  rewrite last_rcons; move/eqmxP=> eqU'V; case/mx_series_rcons=> compU _ maxUm'.
  exists (rcons U' V); last by rewrite last_rcons.
  apply/mx_series_rcons; split => //; exact: max_submod_eqmx maxUm'.
set Um' := last 0 U in maxUm eqUV; have [modU _] := compU.
have modUm': modG Um' by rewrite /Um' (last_nth 0) mx_subseries_module'.
have [|||W compW lastW] := IHU (V :&: Um')%MS; rewrite ?capmx_module //.
  by case: (mx_butterfly modUm' modV modUm); rewrite ?eqUV // {1}capmxC.
exists (rcons W V); last by rewrite last_rcons.
apply/mx_series_rcons; split; rewrite // lastW.
by case: (mx_butterfly modV modUm' modUm); rewrite // andbC eqUV.
Qed.

Let rsim_rcons : forall U V compU compUV i, i < size U ->
  mx_rsim (@series_repr U i compU) (@series_repr (rcons U V) i compUV).
Proof.
move=> U V compU compUV i ltiU.
by apply: subfact_eqmx; rewrite -?rcons_cons nth_rcons ?leqW ?ltiU.
Qed.

Let last_mod : forall U (compU : mx_series U), modG (last 0 U).
Proof.
by move=> U [modU _]; rewrite (last_nth 0) (mx_subseries_module' _ modU).
Qed.

Let rsim_last : forall U V modUm modV compUV,
  mx_rsim (@subfact_repr (last 0 U) V modUm modV)
          (@series_repr (rcons U V) (size U) compUV).
Proof.
move=> U V ? ? ?; apply: subfact_eqmx; last by rewrite nth_rcons ltnn eqxx.
by rewrite -rcons_cons nth_rcons leqnn -last_nth.
Qed.
Local Notation rsimT := mx_rsim_trans.
Local Notation rsimC := mx_rsim_sym.

Lemma mx_JordanHolder : forall U V compU compV (m := size U),
    (last 0 U :=: last 0 V)%MS -> 
  m = size V  /\ (exists p : 'S_m, forall i : 'I_m,
     mx_rsim (@series_repr U i compU) (@series_repr V (p i) compV)).
Proof.
move=> U V /=; elim: {U}(size U) {-2}U V (eqxx (size U)) => [|r IHr] U V.
  move/nilP->; case/lastP: V => [|V Vm] /= ? compVm; rewrite ?last_rcons => Vm0.
    by split=> //; exists 1%g; case.
  by case/mx_series_rcons: (compVm) => _ _ []; rewrite -(lt_eqmx Vm0) ltmx0.
case/lastP: U => // [U Um]; rewrite size_rcons eqSS => szUr compUm.
case/mx_series_rcons: (compUm); set Um' := last 0 U => compU modUm maxUm.
case/lastP: V => [|V Vm] compVm; rewrite ?last_rcons ?size_rcons /= => eqUVm.
  by case/mx_series_rcons: (compUm) => _ _ []; rewrite (lt_eqmx eqUVm) ltmx0.
case/mx_series_rcons: (compVm); set Vm' := last 0 V => compV modVm maxVm.
have [modUm' modVm']: modG Um' * modG Vm' := (last_mod compU, last_mod compV).
pose i_m := @ord_max (size U).
case: (@eqmxP _ _ _ _ Um' Vm') => [eqUVm' |]; last move/eqmxP=> neqUVm'.
  have [szV [p sim_p]] := IHr U V szUr compU compV eqUVm'.
  split; first by rewrite szV.
  exists (lift_perm i_m i_m p) => i; case: (unliftP i_m i) => [j|] ->{i}.
    apply: rsimT (rsimC _) (rsimT (sim_p j) _).
      by rewrite lift_max; exact: rsim_rcons.
    by rewrite lift_perm_lift lift_max; apply: rsim_rcons; rewrite -szV.
  have simUVm := subfact_eqmx modUm' modVm' modUm modVm eqUVm' eqUVm.
  apply: rsimT (rsimC _) (rsimT simUVm _); first exact: rsim_last.
  by rewrite lift_perm_id /= szV; exact: rsim_last.
have maxVUm: max_submod Vm' Um by exact: max_submod_eqmx (eqmx_sym _) maxVm.
have [] := mx_butterfly modUm' modVm' modUm neqUVm' maxUm maxVUm.
move: (capmx_module _ _); set Wm := (Um' :&: Vm')%MS => modWm maxWUm simWVm.
have [|] := mx_butterfly modVm' modUm' modUm _ maxVUm maxUm.
  by rewrite andbC.
move: (capmx_module _ _); rewrite capmxC -/Wm => modWmV maxWVm.
rewrite {modWmV}(bool_irrelevance modWmV modWm) => simWUm.
have [W compW lastW] := mx_JordanHolder_exists compU modWm maxWUm.
have compWU: mx_series (rcons W Um') by apply/mx_series_rcons; rewrite lastW.
have compWV: mx_series (rcons W Vm') by apply/mx_series_rcons; rewrite lastW.
have [|szW [pU pUW]] := IHr U _ szUr compU compWU; first by rewrite last_rcons.
rewrite size_rcons in szW; have ltWU: size W < size U by rewrite -szW.
have{IHr} := IHr _ V _ compWV compV; rewrite last_rcons size_rcons -szW.
case=> {r szUr}// szV [pV pWV]; split; first by rewrite szV.
pose j_m := Ordinal ltWU; pose i_m' := lift i_m j_m.
exists (lift_perm i_m i_m pU * tperm i_m i_m' * lift_perm i_m i_m pV)%g => i.
rewrite !permM; case: (unliftP i_m i) => [j {simWUm}|] ->{i}; last first.
  rewrite lift_perm_id tpermL lift_perm_lift lift_max {simWVm}.
  apply: rsimT (rsimT (pWV j_m) _); last by apply: rsim_rcons; rewrite -szV.
  apply: rsimT (rsimC _) {simWUm}(rsimT simWUm _); first exact: rsim_last.
  by rewrite -lastW in modWm *; exact: rsim_last.
apply: rsimT (rsimC _) {pUW}(rsimT (pUW j) _).
  by rewrite lift_max; exact: rsim_rcons.
rewrite lift_perm_lift; case: (unliftP j_m (pU j)) => [k|] ->{j pU}.
  rewrite tpermD ?(inj_eq (@lift_inj _ _)) ?neq_lift //.
  rewrite lift_perm_lift !lift_max; set j := lift j_m k.
  have ltjW: j < size W by have:= ltn_ord k; rewrite -(lift_max k) /= {1 3}szW.
  apply: rsimT (rsimT (pWV j) _); last by apply: rsim_rcons; rewrite -szV.
  by apply: rsimT (rsimC _) (rsim_rcons compW _ _); first exact: rsim_rcons.
apply: rsimT {simWVm}(rsimC (rsimT simWVm _)) _.
  by rewrite -lastW in modWm *; exact: rsim_last.
rewrite tpermR lift_perm_id /= szV.
by apply: rsimT (rsim_last modVm' modVm _); exact: subfact_eqmx.
Qed.

Lemma mx_JordanHolder_max : forall U (m := size U) V compU modV,
    (last 0 U :=: 1%:M)%MS -> mx_irreducible (@factmod_repr _ G n rG V modV) ->
  exists i : 'I_m, mx_rsim (factmod_repr modV) (@series_repr U i compU).
Proof.
move=> /= U V compU modV; set Um := last 0 U => Um1 irrV.
have modUm: modG Um := last_mod compU; have simV := rsimC (mx_factmod_sub modV).
have maxV: max_submod V Um.
  move/max_submodP: (mx_rsim_irr simV irrV); move/(_ (subsetmx1 _)).
  by apply: max_submod_eqmx; last exact: eqmx_sym.
have [W compW lastW] := mx_JordanHolder_exists compU modV maxV.
have compWU: mx_series (rcons W Um) by apply/mx_series_rcons; rewrite lastW.
have:= mx_JordanHolder compU compWU; rewrite last_rcons size_rcons.
case=> // szW [p pUW]; have ltWU: size W < size U by rewrite szW.
pose i := Ordinal ltWU; exists ((p^-1)%g i).
apply: rsimT simV (rsimT _ (rsimC (pUW _))); rewrite permKV.
apply: rsimT (rsimC _) (rsim_last (last_mod compW) modUm _).
by apply: subfact_eqmx; rewrite ?lastW.
Qed.

End JordanHolder.

Section Regular.

Variables (gT : finGroupType) (G : {group gT}).
Local Notation nG := #|pred_of_set (gval G)|.

Definition gring_index (x : gT) := enum_rank_in (group1 G) x.

Lemma gring_valK : cancel enum_val gring_index.
Proof. exact: enum_valK_in. Qed.

Lemma gring_indexK : {in G, cancel gring_index enum_val}.
Proof. exact: enum_rankK_in. Qed.
  
Definition regular_mx x : 'M[F]_nG :=
  \matrix_i delta_mx 0 (gring_index (enum_val i * x)).

Lemma regular_mx_repr : mx_repr G regular_mx.
Proof.
split=> [|x y Gx Gy]; apply/row_matrixP=> i; rewrite !rowK.
  by rewrite mulg1 row1 gring_valK. 
by rewrite row_mul rowK -rowE rowK mulgA gring_indexK // groupM ?enum_valP.
Qed.
Canonical Structure regular_repr := MxRepresentation regular_mx_repr.
Local Notation aG := regular_repr.
Definition group_ring := enveloping_algebra_mx aG.
Local Notation R_G := group_ring.

Lemma gring_free : row_free R_G.
Proof.
apply/row_freeP; exists (lin1_mx (row (gring_index 1) \o vec_mx)).
apply/row_matrixP=> i; rewrite row_mul rowK mul_rV_lin1 /= mxvecK rowK row1.
by rewrite gring_indexK // mul1g gring_valK.
Qed.

Definition gring_row : 'M[F]_nG -> 'rV_nG := row (gring_index 1).
Canonical Structure gring_row_linear := [linear of gring_row].

Lemma gring_row_mul : forall A B, gring_row (A *m B) = gring_row A *m B.
Proof. by move=> A B; exact: row_mul. Qed.

Definition gring_proj x := row (gring_index x) \o trmx \o gring_row.
Canonical Structure gring_proj_linear x := [linear of gring_proj x].

Lemma gring_projE : {in G &, forall x y, gring_proj x (aG y) = (x == y)%:R}.
Proof.
move=> x y Gx Gy; rewrite /gring_proj /= /gring_row rowK gring_indexK //=.
rewrite mul1g trmx_delta rowE mul_delta_mx_cond [delta_mx 0 0]mx11_scalar !mxE.
by rewrite /= -(inj_eq (can_inj gring_valK)) !gring_indexK.
Qed.

Section GringMx.

Variables (n : nat) (rG : mx_representation G n).

Definition gring_mx := vec_mx \o mulmxr (enveloping_algebra_mx rG).
Canonical Structure gring_mx_linear := [linear of gring_mx].

Lemma gring_mxP : forall a, (gring_mx a \in enveloping_algebra_mx rG)%MS.
Proof. by move=> a; rewrite vec_mxK subsetmxMl. Qed.

Lemma gring_mxJ : forall a x,
  x \in G -> gring_mx (a *m aG x) = gring_mx a *m rG x.
Proof.
move=> a x Gx; rewrite /gring_mx /= ![a *m _]mulmx_sum_row.
rewrite !(mulmx_suml, linear_sum); apply: eq_bigr => i _.
rewrite linearZ -!scalemxAl linearZ; congr (_ *m: _) => {a}.
rewrite !rowK /= !mxvecK -rowE rowK mxvecK.
by rewrite gring_indexK ?groupM ?repr_mxM ?enum_valP.
Qed.

Definition gring_op := gring_mx \o gring_row.
Canonical Structure gring_op_linear := [linear of gring_op].

Lemma gring_opE : forall a, gring_op a = gring_mx (gring_row a).
Proof. by []. Qed.

Lemma gring_opG : forall x, x \in G -> gring_op (aG x) = rG x.
Proof.
move=> x Gx; rewrite /gring_op /= /gring_row rowK gring_indexK // mul1g.
by rewrite /gring_mx /= -rowE rowK mxvecK gring_indexK.
Qed.

Lemma gring_opM : forall A B,
  (B \in R_G)%MS -> gring_op (A *m B) = gring_op A *m gring_op B.
Proof.
move=> A B; case/envelop_mxP=> b ->{B}; rewrite !linear_sum.
apply: eq_bigr => x Gx; rewrite !linearZ /= gring_opG //.
by rewrite -gring_mxJ // -gring_row_mul.
Qed.

Hypothesis irrG : mx_irreducible rG.

Lemma rsim_regular_factmod :
  {U : 'M_nG & {modU : mxmodule aG U & mx_rsim rG (factmod_repr modU)}}.
Proof.
pose v : 'rV[F]_n := nz_row 1%:M.
pose fU := lin1_mx (mulmx v \o gring_mx); pose U := kermx fU.
have modU: mxmodule aG U.
  apply/mxmoduleP => x Gx; apply/sub_kermxP; apply/row_matrixP=> i.
  rewrite 2!row_mul row0; move: (row i U) (sub_kermxP (row_sub i U)) => u.
  by rewrite !mul_rV_lin1 /= gring_mxJ // mulmxA => ->; rewrite mul0mx.
have def_n: \rank (cokermx U) = n.
  rewrite mxrank_coker mxrank_ker subKn ?rank_leq_row // -genmxE.
  have [_ _ ->] := irrG; rewrite ?mxrank1 ?subsetmx1 //.
    rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
    apply/row_subP=> i; apply: eq_row_sub (gring_index (enum_val i * x)) _.
    rewrite !rowE mulmxA !mul_rV_lin1 /= -mulmxA -gring_mxJ //.
    by rewrite -rowE rowK.
  rewrite (eqmx_eq0 (genmxE _)); apply/rowV0Pn.
  exists v; last exact: (nz_row_mxsimple irrG).
  apply/subsetmxP; exists (gring_row (aG 1%g)); rewrite mul_rV_lin1 /=.
  by rewrite -gring_opE gring_opG // repr_mx1 mulmx1.
exists U; exists modU; apply: mx_rsim_sym.
exists (val_factmod 1%:M *m fU) => // [|x Gx].
  rewrite /row_free eqn_leq rank_leq_row /= -subn_eq0 -mxrank_ker mxrank_eq0.
  apply/rowV0P=> u; move/sub_kermxP; rewrite mulmxA; move/sub_kermxP.
  by rewrite -/U -in_factmod_eq0 mulmxA mulmx1 val_factmodK; move/eqP.
rewrite mulmxA -val_factmodE (canRL (addKr _) (add_sub_fact_mod U _)).
rewrite mulmx_addl mulNmx (sub_kermxP _) ?val_submodP // addrC subr0.
apply/row_matrixP=> i; move: (val_factmod _) => zz.
by rewrite !row_mul !mul_rV_lin1 /= gring_mxJ // mulmxA.
Qed.

Lemma rsim_regular_series : forall U (compU : mx_composition_series aG U),
    (last 0 U :=: 1%:M)%MS ->
  exists i : 'I_(size U), mx_rsim rG (series_repr i compU).
Proof.
move=> U compU lastU; have [V [modV simGV]] := rsim_regular_factmod.
have irrV := mx_rsim_irr simGV irrG.
have [i simVU] := mx_JordanHolder_max compU lastU irrV.
exists i; exact: mx_rsim_trans simGV simVU.
Qed.

Hypothesis F'G : [char F]^'.-group G.

Lemma rsim_regular_submod :
  {U : 'M_nG & {modU : mxmodule aG U & mx_rsim rG (submod_repr modU)}}.
Proof.
have [V [modV eqG'V]] := rsim_regular_factmod.
have [U modU defVU dxVU] := mx_Maeshke F'G modV (subsetmx1 V).
have eqUV: \rank U = \rank (cokermx V).
  by rewrite mxrank_coker -{3}(mxrank1 F #|G|) -defVU (mxdirectP dxVU) addKn.
have{dxVU} dxUV: (U :&: V = 0)%MS by rewrite capmxC; exact/mxdirect_addsP.
exists U; exists modU; apply: mx_rsim_trans eqG'V _.
exists (in_submod U (val_factmod 1%:M *m proj_mx U V)) => // [|x Gx].
  rewrite /row_free -{6}eqUV -[_ == _]subset1mx -val_submodS val_submod1.
  rewrite in_submodK ?proj_mx_sub // -{1}[U](proj_mx_id dxUV) //.
  rewrite -{1}(add_sub_fact_mod V U) mulmx_addl proj_mx_0 ?val_submodP // add0r.
  by rewrite subsetmxMr // val_factmodS subsetmx1.
rewrite -in_submodJ ?proj_mx_sub // -(hom_mxP _) //; last first.
  by apply: subsetmx_trans (subsetmx1 _) _; rewrite -defVU addsmxC proj_mx_hom.
rewrite mulmxA; congr (_ *m _); rewrite mulmxA -val_factmodE; apply/eqP.
rewrite eq_sym -subr_eq0 -mulmx_subl proj_mx_0 //.
by rewrite -[_ *m aG x](add_sub_fact_mod V) addrK val_submodP.
Qed.

End GringMx.

Lemma gring_mxK : cancel (gring_mx aG) gring_row.
Proof.
move=> a; rewrite /gring_mx /= mulmx_sum_row !linear_sum.
rewrite {2}[a]row_sum_delta; apply: eq_bigr => i _.
rewrite !linearZ /= /gring_row !(rowK, mxvecK).
by rewrite gring_indexK // mul1g gring_valK.
Qed.

Lemma gring_mxA : forall n (rG : mx_representation G n) a b,
  gring_mx rG (a *m gring_mx aG b) = gring_mx rG a *m gring_mx rG b.
Proof.
move=> n rG a b; rewrite -{1}[a]gring_mxK -row_mul -gring_opE.
by rewrite gring_opM ?gring_mxP // /gring_op /= !gring_mxK.
Qed.

Lemma gring_op_id : forall A, (A \in R_G)%MS -> gring_op aG A = A.
Proof.
move=> A; case/envelop_mxP=> a ->{A}; rewrite linear_sum.
by apply: eq_bigr => x Gx; rewrite linearZ /= gring_opG.
Qed.

Lemma gring_rowK : forall A, (A \in R_G)%MS -> gring_mx aG (gring_row A) = A.
Proof. exact gring_op_id. Qed.

Lemma mem_gring_mx : forall m a (M : 'M_(m, nG)),
  (gring_mx aG a \in M *m R_G)%MS = (a <= M)%MS.
Proof. by move=> m a M; rewrite vec_mxK subsetmxMfree ?gring_free. Qed.

Lemma mem_sub_gring : forall m A (M : 'M_(m, nG)),
  (A \in M *m R_G)%MS = (A \in R_G)%MS && (gring_row A <= M)%MS.
Proof.
move=> m A M; rewrite -(andb_idl (memmx_subP (subsetmxMl _ _) A)).
by apply: andb_id2l => R_A; rewrite -mem_gring_mx gring_rowK.
Qed.

Definition gset_mx (A : {set gT}) := \sum_(x \in A) aG x.

Local Notation tG := #|pred_of_set (classes G)|.

Definition classg_base := \matrix_(k < tG) mxvec (gset_mx (enum_val k)).

Let groupCl : {in G, forall x, {subset x ^: G <= G}}.
Proof. by move=> x Gx; apply: subsetP; exact: class_subG. Qed.

Lemma classg_base_free : row_free classg_base.
Proof.
rewrite -kermx_eq0; apply/rowV0P=> v; move/sub_kermxP.
rewrite mulmx_sum_row => v0; apply/rowP=> k; rewrite mxE.
have [x Gx def_k] := imsetP (enum_valP k).
transitivity (gring_proj x (vec_mx 0) 0 0); last by rewrite !linear0 !mxE.
rewrite -{}v0 !linear_sum (bigD1 k) //= !linearZ /= rowK mxvecK def_k.
rewrite linear_sum (bigD1 x) ?class_refl //= gring_projE // eqxx.
rewrite !big1 ?addr0 ?mxE ?mulr1 // => [k' | y]; first 1 last.
  case/andP=> xGy ne_yx.
  by rewrite gring_projE ?(groupCl Gx xGy) // eq_sym (negPf ne_yx).
rewrite rowK !linearZ /= mxvecK -(inj_eq (@enum_val_inj _ _)) def_k eq_sym.
have [z Gz ->] := imsetP (enum_valP k'); move/eqP=> not_Gxz.
rewrite linear_sum big1 ?linear0 //= => y zGy.
rewrite gring_projE ?(groupCl Gz zGy) //.
by case: eqP zGy => // <-; move/class_transr.
Qed.

Lemma classg_base_center : (classg_base :=: 'Z(R_G))%MS.
Proof.
apply/eqmxP; apply/andP; split.
  apply/row_subP=> k; rewrite rowK /gset_mx sub_capmx {1}linear_sum.
  have [x Gx ->{k}] := imsetP (enum_valP k); have sxGG := groupCl Gx.
  rewrite summx_sub => [|y xGy]; last by rewrite envelop_mx_id ?sxGG.
  rewrite memmx_cent_envelop; apply/centgmxP=> y Gy.
  rewrite {2}(reindex_acts 'J _ Gy) ?astabsJ ?class_normG //=.
  rewrite mulmx_suml mulmx_sumr; apply: eq_bigr => z; move/sxGG=> Gz.
  by rewrite -!repr_mxM ?groupJ -?conjgC.
apply/memmx_subP=> A; rewrite sub_capmx memmx_cent_envelop.
case/andP; case/envelop_mxP=> a ->{A} cGa.
rewrite (partition_big_imset (class^~ G)) -/(classes G) /=.
rewrite linear_sum summx_sub //= => xG GxG; have [x Gx def_xG] := imsetP GxG.
apply: subsetmx_trans (scalemx_sub (a x) (subsetmx_refl _)).
rewrite (eq_row_sub (enum_rank_in GxG xG)) // linearZ /= rowK enum_rankK_in //.
rewrite !linear_sum {xG GxG}def_xG; apply: eq_big => [y | xy] /=.
  apply/idP/andP=> [| [_ xGy]]; last by rewrite -(eqP xGy) class_refl.
  by case/imsetP=> z Gz ->; rewrite groupJ // classGidl.
case/imsetP=> y Gy ->{xy}; rewrite linearZ; congr (_ *m: _).
move/(canRL (repr_mxK aG Gy)): (centgmxP cGa y Gy); have Gy' := groupVr Gy.
move/(congr1 (gring_proj x)); rewrite -mulmxA mulmx_suml !linear_sum.
rewrite (bigD1 x Gx) big1 => [|z]; rewrite !linearZ /=; last first.
  case/andP=> Gz; rewrite eq_sym gring_projE //.
  by move/negPf->; rewrite linear0.
rewrite gring_projE // eqxx scalemx1 (bigD1 (x ^ y)%g) ?groupJ //=.
rewrite big1 => [|z]; rewrite -scalemxAl !linearZ /=.
  rewrite !addr0 -!repr_mxM ?groupM // mulgA mulKVg mulgK.
  by move/rowP; move/(_ 0); rewrite gring_projE // eqxx scalemx1 !mxE.
case/andP=> Gz; rewrite eq_sym -(can_eq (conjgKV y)) conjgK conjgE invgK.
by rewrite -!repr_mxM ?gring_projE ?groupM //; move/negPf->; rewrite linear0.
Qed.

Lemma regular_module_ideal : forall m (M : 'M_(m, nG)),
  mxmodule aG M = right_mx_ideal R_G (M *m R_G).
Proof.
move=> m M; apply/idP/idP=> modM.
  apply/mulsmx_subP=> A B; rewrite !mem_sub_gring; case/andP=> R_A M_A R_B.
  by rewrite envelop_mxM // gring_row_mul (mxmodule_envelop modM).
apply/mxmoduleP=> x Gx; apply/row_subP=> i; rewrite row_mul -mem_gring_mx.
rewrite gring_mxJ // (mulsmx_subP modM) ?envelop_mx_id //.
by rewrite mem_gring_mx row_sub.
Qed.

Variable sG : socleType aG.

Definition Wedderburn_subring (i : sG) := <<i *m R_G>>%MS.

Local Notation R_ := Wedderburn_subring.

Let sums_R : (\sum_i R_ i :=: Socle sG *m R_G)%MS.
Proof.
apply/eqmxP; set R_S := (_ <= _)%MS.
have sRS : R_S.
  by apply/sumsmx_subP=> i; rewrite genmxE subsetmxMr ?(sumsmx_sup i).
rewrite sRS -(mulmxKpV sRS) mulmxA subsetmxMr //; apply/sumsmx_subP=> i _.
rewrite -(subsetmxMfree _ _ gring_free) -(mulmxA _ _ R_G) mulmxKpV //.
by rewrite (sumsmx_sup i) ?genmxE.
Qed.

Lemma Wedderburn_ideal : forall i, mx_ideal R_G (R_ i).
Proof.
move=> i; apply/andP; split; last first.
  rewrite /right_mx_ideal genmxE (muls_eqmx (genmxE _) (eqmx_refl _)).
  by rewrite -[(_ <= _)%MS]regular_module_ideal component_mx_module.
apply/mulsmx_subP=> A B R_A.
rewrite !genmxE !mem_sub_gring; case/andP=> R_B SiB.
rewrite envelop_mxM {R_A}// gring_row_mul -{R_B}(gring_rowK R_B).
pose f := mulmx (gring_row A) \o gring_mx aG.
rewrite -[_ *m _](mul_rV_lin1 [linear of f]).
suffices: (i *m lin1_mx f <= i)%MS by apply: subsetmx_trans; rewrite subsetmxMr.
apply: hom_component_mx; first exact: socle_simple.
apply/rV_subP=> v _; apply/hom_mxP=> x Gx.
by rewrite !mul_rV_lin1 /f /= gring_mxJ ?mulmxA.
Qed.

Lemma Wedderburn_direct : mxdirect (\sum_i R_ i)%MS.
Proof.
apply/mxdirectP; rewrite /= sums_R mxrankMfree ?gring_free //.
rewrite (mxdirectP (Socle_direct sG)); apply: eq_bigr=> i _ /=.
by rewrite genmxE mxrankMfree ?gring_free.
Qed.

Lemma Wedderburn_disjoint : forall i j, i != j -> (R_ i :&: R_ j)%MS = 0.
Proof.
move=> i j ne_ij; apply/eqP; rewrite -subsetmx0 capmxC.
by rewrite -(mxdirect_sumsP Wedderburn_direct j) // capmxS // (sumsmx_sup i).
Qed.

Lemma Wedderburn_annihilate : forall i j, i != j -> (R_ i * R_ j)%MS = 0.
Proof.
move=> i j ne_ij; apply/eqP; rewrite -subsetmx0 -(Wedderburn_disjoint ne_ij).
rewrite sub_capmx; apply/andP; split.
  case/andP: (Wedderburn_ideal i) => _; apply: subsetmx_trans.
  by rewrite mulsmxS // genmxE subsetmxMl.
case/andP: (Wedderburn_ideal j) => idlRj _; apply: subsetmx_trans idlRj.
by rewrite mulsmxS // genmxE subsetmxMl.
Qed.

Lemma Wedderburn_mulmx0 : forall i j A B,
  i != j -> (A \in R_ i)%MS -> (B \in R_ j)%MS -> A *m B = 0.
Proof.
move=> i j A B ne_ij RiA RjB; apply: memmx0.
by rewrite -(Wedderburn_annihilate ne_ij) mem_mulsmx.
Qed.

Lemma rfix_regular : (rfix_mx aG G :=: gring_row (gset_mx G))%MS.
Proof.
apply/eqmxP; apply/andP; split; last first.
  apply/rfix_mxP => x Gx; rewrite -gring_row_mul; congr gring_row.
  rewrite {2}/gset_mx (reindex_astabs 'R x) ?astabsR //= mulmx_suml.
  by apply: eq_bigr => y Gy; rewrite repr_mxM.
apply/rV_subP=> v; move/rfix_mxP=> cGv.
have: (gring_mx aG v \in R_G)%MS by rewrite vec_mxK subsetmxMl.
case/envelop_mxP=> a def_v.
suffices ->: v = a 1%g *m: gring_row (gset_mx G) by rewrite scalemx_sub.
rewrite -linearZ linear_sum -[v]gring_mxK def_v; congr (gring_row _).
apply: eq_bigr => x Gx; congr (_ *m: _).
move/rowP: (congr1 (gring_proj x \o gring_mx aG) (cGv x Gx)); move/(_ 0).
rewrite /= gring_mxJ // def_v mulmx_suml !linear_sum (bigD1 1%g) //=.
rewrite repr_mx1 -scalemxAl mul1mx linearZ /= gring_projE // eqxx scalemx1.
rewrite big1 ?addr0 ?mxE /= => [ | y]; last first.
  case/andP=> Gy nt_y; rewrite -scalemxAl linearZ -repr_mxM //=.
  by rewrite gring_projE ?groupM // eq_sym eq_mulgV1 mulgK (negPf nt_y) linear0.
rewrite (bigD1 x) //= linearZ /= gring_projE // eqxx scalemx1.
rewrite big1 ?addr0 ?mxE // => y; case/andP=> Gy ne_yx.
by rewrite linearZ /= gring_projE // eq_sym (negPf ne_yx) linear0.
Qed.

Lemma principal_comp_subproof : mxsimple aG (rfix_mx aG G).
Proof.
apply: linear_mxsimple; first exact: rfix_mx_module.
apply/eqP; rewrite rfix_regular eqn_leq rank_leq_row lt0n mxrank_eq0.
apply/eqP; move/(congr1 (gring_proj 1 \o gring_mx aG)); apply/eqP.
rewrite /= -[gring_mx _ _]/(gring_op _ _) !linear0 !linear_sum (bigD1 1%g) //=.
rewrite gring_opG // gring_projE // eqxx big1 ?addr0 ?oner_eq0 // => x.
by case/andP=> Gx nt_x; rewrite gring_opG // gring_projE // eq_sym (negPf nt_x).
Qed.

Definition principal_comp :=
  locked (PackSocle (component_socle sG principal_comp_subproof)).

Lemma principal_comp_rfix : (principal_comp :=: rfix_mx aG G)%MS.
Proof.
unlock principal_comp; rewrite PackSocleK; apply/eqmxP.
rewrite (component_mx_id principal_comp_subproof) andbT.
have [I [W isoW ->]] := component_mx_def principal_comp_subproof.
apply/sumsmx_subP=> i _; have [f _ hom_f <-]:= isoW i.
by apply/rfix_mxP=> x Gx; rewrite -(hom_mxP hom_f) // (rfix_mxP G _).
Qed.

Lemma rank_principal_comp : \rank principal_comp = 1%N.
Proof.
apply/eqP; rewrite eqn_leq lt0n mxrank_eq0 nz_socle andbT.
by rewrite principal_comp_rfix rfix_regular rank_leq_row.
Qed.

Hypothesis F'G : [char F]^'.-group G.

Lemma Wedderburn_sum : (\sum_i R_ i :=: R_G)%MS.
Proof.
apply: eqmx_trans sums_R _; rewrite reducible_Socle1 ?mul1mx //.
exact: mx_Maeshke.
Qed.

Definition Wedderburn_id_mx i :=
  vec_mx (mxvec 1%:M *m proj_mx (R_ i) (\sum_(j | j != i) R_ j)%MS).

Local Notation e_ := Wedderburn_id_mx.

Lemma Wedderburn_sum_id : \sum_i e_ i = 1%:M.
Proof.
rewrite -linear_sum; apply: canLR mxvecK _.
have: (1%:M \in R_G)%MS := envelop_mx1 aG.
rewrite -Wedderburn_sum; case/(sub_bigdaddsmx Wedderburn_direct) => e Re -> _.
apply: eq_bigr => i _; have dxR := mxdirect_sumsP Wedderburn_direct i (erefl _).
rewrite (bigD1 i) // mulmx_addl proj_mx_id ?Re // proj_mx_0 ?addr0 //=.
by rewrite summx_sub // => j ne_ji; rewrite (sumsmx_sup j) ?Re.
Qed.

Lemma Wedderburn_id_mem : forall i, (e_ i \in R_ i)%MS.
Proof. by move=> i; rewrite vec_mxK proj_mx_sub. Qed.

Lemma Wedderburn_is_id : forall i, mxring_id (R_ i) (e_ i).
Proof.
move=> i; have ideRi: forall A, (A \in R_ i)%MS -> e_ i *m A = A.
  move=> A RiA; rewrite -{2}[A]mul1mx -Wedderburn_sum_id mulmx_suml.
  rewrite (bigD1 i) //= big1 ?addr0 // => j ne_ji.
  by rewrite (Wedderburn_mulmx0 ne_ji) ?Wedderburn_id_mem.
  split=> // [||A RiA]; first 2 [exact: Wedderburn_id_mem].
  apply: contra (nz_socle i); move/eqP=> e0.
  apply/rowV0P=> v; rewrite -mem_gring_mx -(genmxE (i *m _)); move/ideRi.
  by rewrite e0 mul0mx; move/(canLR gring_mxK); rewrite linear0.
rewrite -{2}[A]mulmx1 -Wedderburn_sum_id mulmx_sumr (bigD1 i) //=.
rewrite big1 ?addr0 // => j; rewrite eq_sym => ne_ij.
by rewrite (Wedderburn_mulmx0 ne_ij) ?Wedderburn_id_mem.
Qed.

Lemma Wedderburn_closed : forall i, (R_ i * R_ i = R_ i)%MS.
Proof.
move=> i; rewrite -{3}[R_ i]genmx_id -/(R_ i) -genmx_muls; apply/genmxP.
have [idlRi idrRi] := andP (Wedderburn_ideal i).
apply/andP; split.
  by apply: subsetmx_trans idrRi; rewrite mulsmxS // genmxE subsetmxMl.
have [_ Ri_e ideRi _] := Wedderburn_is_id i.
by apply/memmx_subP=> A RiA; rewrite -[A]ideRi ?mem_mulsmx.
Qed.

Lemma Wedderburn_is_ring : forall i, mxring (R_ i).
Proof.
move=> i; rewrite /mxring /left_mx_ideal Wedderburn_closed subsetmx_refl.
apply/mxring_idP; exists (e_ i); exact: Wedderburn_is_id.
Qed.

Lemma Wedderburn_min_ideal : forall m i (E : 'A_(m, nG)),
  E != 0 -> (E <= R_ i)%MS -> mx_ideal R_G E -> (E :=: R_ i)%MS.
Proof.
move=> m i E nzE sE_Ri; case/andP=> idlE idrE; apply/eqmxP; rewrite sE_Ri.
pose M := E *m pinvmx R_G; have defE: E = M *m R_G.
  by rewrite mulmxKpV // (subsetmx_trans sE_Ri) // genmxE subsetmxMl.
have modM: mxmodule aG M by rewrite regular_module_ideal -defE.
have simSi := socle_simple i; set Si := socle_base i in simSi.
have [I [W isoW defW]]:= component_mx_def simSi; rewrite /R_ /socle_val /= defW.
rewrite genmxE defE subsetmxMr //; apply/sumsmx_subP=> j _.
have simW := mx_iso_simple (isoW j) simSi; have [modW _ minW] := simW.
case: (eqVneq (W j :&: M)%MS 0) => [{minW}dxWE | nzWE]; last first.
  by move/minW: nzWE => <-; rewrite ?capmxSl ?capmxSr ?capmx_module.
have [_ Rei ideRi _] := Wedderburn_is_id i.
rewrite -subsetmx0 in nzE; case/memmx_subP: nzE => A E_A.
rewrite -(ideRi _ (memmx_subP sE_Ri _ E_A)).
have:= E_A; rewrite defE mem_sub_gring; case/andP=> R_A M_A.
have:= Rei; rewrite genmxE mem_sub_gring; case/andP=> Re.
rewrite -{2}(gring_rowK Re) /socle_val defW; case/sub_sumsmxP=> e ->.
rewrite !(linear_sum, mulmx_suml) summx_sub //= => k _.
rewrite -(gring_rowK R_A) -gring_mxA -mulmxA gring_rowK //.
rewrite ((W k *m _ =P 0) _) ?linear0 ?subset0mx //.
have [f _ homWf defWk] := mx_iso_trans (mx_iso_sym (isoW j)) (isoW k).
rewrite -subsetmx0 -{k defWk}(eqmxMr _ defWk) -(hom_envelop_mxC homWf) //.
rewrite -(mul0mx _ f) subsetmxMr {f homWf}// -dxWE sub_capmx.
rewrite (mxmodule_envelop modW) //=; apply/row_subP=> k.
rewrite row_mul -mem_gring_mx -(gring_rowK R_A) gring_mxA gring_rowK //.
by rewrite -defE (memmx_subP idlE) // mem_mulsmx ?gring_mxP.
Qed.

Section RegularComponent.

(* The component of the socle of the regular module that is associated to an *)
(* irreducible representation.                                               *)

Variables (n : nat) (rG : mx_representation G n).
Local Notation E_G := (enveloping_algebra_mx rG).

Let not_rsim_op0 : forall (iG j : sG) A,
    mx_rsim rG (socle_repr iG) -> iG != j -> (A \in R_ j)%MS ->
  gring_op rG A = 0.
Proof.
move=> iG j A; case/mx_rsim_def=> f [f' _ hom_f] ne_iG_j RjA.
transitivity (f *m in_submod _ (val_submod 1%:M *m A) *m f').
  have{RjA}: (A \in R_G)%MS by rewrite -Wedderburn_sum (sumsmx_sup j).
  case/envelop_mxP=> a ->{A}; rewrite !(linear_sum, mulmx_suml).
  by apply: eq_bigr => x Gx; rewrite !linearZ /= -scalemxAl -hom_f ?gring_opG.
rewrite (_ : _ *m A = 0) ?(linear0, mul0mx) //.
apply/row_matrixP=> i; rewrite row_mul row0 -[row _ _]gring_mxK -gring_row_mul.
rewrite (Wedderburn_mulmx0 ne_iG_j) ?linear0 // genmxE mem_gring_mx.
by rewrite (row_subP _) // val_submod1 component_mx_id //; exact: socle_simple.
Qed.

Definition regular_comp :=
  odflt principal_comp [pick i : sG | gring_op rG (e_ i) != 0].
Local Notation iG := regular_comp.

Hypothesis irrG : mx_irreducible rG.

Lemma rsim_regular_comp : mx_rsim rG (socle_repr iG).
Proof.
have [M [modM rsimM]] := rsim_regular_submod irrG F'G.
have simM: mxsimple aG M.
  case/mx_irrP: irrG => n_gt0 minG.
  have [f def_n injf homf] := mx_rsim_sym rsimM.
  apply/(submod_mx_irr modM); apply/mx_irrP.
  split=> [|U modU nzU]; first by rewrite def_n.
  rewrite /row_full -(mxrankMfree _ injf) -genmxE {4}def_n.
  apply: minG; last by rewrite -mxrank_eq0 genmxE mxrankMfree // mxrank_eq0.
  rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
  by rewrite -mulmxA -homf // mulmxA subsetmxMr // (mxmoduleP modU).
pose i := PackSocle (component_socle sG simM).
have{modM rsimM} rsimM: mx_rsim rG (socle_repr i).
  apply: mx_rsim_trans rsimM (mx_rsim_sym _); apply/mx_rsim_iso.
  apply: (component_mx_iso (socle_simple _)) => //.
  by rewrite [component_mx _ _]PackSocleK component_mx_id.
case: (eqVneq i iG) => [<- // | ne_i_iG].
suffices {i M simM ne_i_iG rsimM}: gring_op rG (e_ iG) != 0.
  by rewrite (not_rsim_op0 rsimM ne_i_iG) ?Wedderburn_id_mem ?eqxx.
rewrite /iG; case: pickP => //= G0.
suffices: rG 1%g == 0.
  by case/idPn; rewrite -mxrank_eq0 repr_mx1 mxrank1 -lt0n; case/mx_irrP: irrG.
rewrite -gring_opG // repr_mx1 -Wedderburn_sum_id linear_sum big1 // => j _.
by move/eqP: (G0 j).
Qed.

Lemma regular_comp'_op0 : forall j A,
  j != iG -> (A \in R_ j)%MS -> gring_op rG A = 0.
Proof. move=> j A; rewrite eq_sym; exact: not_rsim_op0 rsim_regular_comp. Qed.

Lemma regular_comp_envelop : (R_ iG *m lin_mx (gring_op rG) :=: E_G)%MS.
Proof.
apply/eqmxP; apply/andP; split; apply/row_subP=> i.
  by rewrite row_mul mul_rV_lin gring_mxP.
rewrite rowK /= -gring_opG ?enum_valP // -mul_vec_lin -gring_opG ?enum_valP //.
rewrite vec_mxK /= -mulmxA mulmx_sub {i}//= -(eqmxMr _ Wedderburn_sum).
rewrite (bigD1 iG) //= addsmxMr addsmxC [_ *m _](sub_kermxP _) ?adds0mx //=.
apply/sumsmx_subP => j ne_j_iG; apply/memmx_subP=> A RjA; apply/sub_kermxP.
by rewrite mul_vec_lin /= (regular_comp'_op0 ne_j_iG RjA) linear0.
Qed.

Lemma ker_regular_comp_op : (R_ iG :&: kermx (lin_mx (gring_op rG)))%MS = 0.
Proof.
apply/eqP; rewrite -subsetmx0; apply/memmx_subP=> A.
rewrite sub_capmx /= subsetmx0 mxvec_eq0; case/andP=> R_A.
rewrite (sameP sub_kermxP eqP) mul_vec_lin mxvec_eq0 /= => opA0.
have [_ Re ideR _] := Wedderburn_is_id iG; rewrite -[A]ideR {ideR}//.
move: Re; rewrite genmxE mem_sub_gring /socle_val; case/andP=> Re.
rewrite -{2}(gring_rowK Re) -subsetmx0.
pose simMi := socle_simple iG; have [J [M isoM ->]] := component_mx_def simMi.
case/sub_sumsmxP=> e ->; rewrite linear_sum mulmx_suml summx_sub // => j _.
rewrite -(in_submodK (subsetmxMl _ (M j))); move: (in_submod _ _) => v.
have modMj: mxmodule aG (M j) by apply: mx_iso_module (isoM j) _; case: simMi.
have rsimMj: mx_rsim rG (submod_repr modMj).
  by apply: mx_rsim_trans rsim_regular_comp _; exact/mx_rsim_iso.
have [f [f' _ hom_f]] := mx_rsim_def (mx_rsim_sym rsimMj); rewrite subsetmx0.
have <-: (gring_mx aG (val_submod (v *m (f *m gring_op rG A *m f')))) = 0.
  by rewrite (eqP opA0) !(mul0mx, linear0).
have: (A \in R_G)%MS by rewrite -Wedderburn_sum (sumsmx_sup iG).
case/envelop_mxP=> a ->; rewrite !(linear_sum, mulmx_suml) /=; apply/eqP.
apply: eq_bigr=> x Gx; rewrite !linearZ -scalemxAl !linearZ /=.
by rewrite gring_opG // -hom_f // val_submodJ // gring_mxJ.
Qed.

Lemma regular_op_inj :
  {in [pred A | A \in R_ iG]%MS &, injective (gring_op rG)}.
Proof.
move=> A B RnA RnB /= eqAB; apply/eqP; rewrite -subr_eq0 -mxvec_eq0 -subsetmx0.
rewrite -ker_regular_comp_op sub_capmx (sameP sub_kermxP eqP) mul_vec_lin.
by rewrite 2!linear_sub /= eqAB subrr linear0 addmx_sub ?eqmx_opp /=.
Qed.

Lemma rank_regular_comp : \rank (R_ iG) = \rank E_G. 
Proof.
symmetry; rewrite -{1}regular_comp_envelop; apply/mxrank_injP.
by rewrite ker_regular_comp_op.
Qed.

End RegularComponent.

Lemma regular_comp_rsim : forall n1 n2 rG1 rG2,
  @mx_rsim _ G n1 rG1 n2 rG2 -> regular_comp rG1 = regular_comp rG2.
Proof.
move=> n1 n2 rG1 rG2 [f eq_n12]; rewrite -eq_n12 in rG2 f * => inj_f hom_f.
congr (odflt _ _); apply: eq_pick => i; rewrite -!mxrank_eq0.
rewrite -(mxrankMfree _ inj_f); symmetry; rewrite -(eqmxMfull _ inj_f).
have: (e_ i \in R_G)%MS.
  by rewrite -Wedderburn_sum (sumsmx_sup i) ?Wedderburn_id_mem.
case/envelop_mxP=> e ->{i}; congr (\rank _ != _).
rewrite !(mulmx_suml, linear_sum); apply: eq_bigr => x Gx.
by rewrite !linearZ -scalemxAl /= !gring_opG ?hom_f.
Qed.

Lemma regular_comp_refl : forall i, regular_comp (socle_repr i) = i.
Proof.
move=> i; apply/eqP; apply/component_mx_isoP; try exact: socle_simple.
by move/mx_rsim_iso: (rsim_regular_comp (socle_irr i)); exact: mx_iso_sym.
Qed.

Lemma regular_comp_id : forall (M : 'M_nG) (modM : mxmodule aG M) (iM : sG),
  mxsimple aG M -> (M <= iM)%MS -> regular_comp (submod_repr modM) = iM.
Proof.
move=> M modM iM simM sMiM; rewrite -[iM]regular_comp_refl.
symmetry; apply: regular_comp_rsim; apply/mx_rsim_iso.
by apply: component_mx_iso => //; exact: socle_simple.
Qed.

Hypothesis splitG : group_splitting_field G.

Definition Wedderburn_degree (i : sG) := \rank (socle_base i).

Local Notation n_ := Wedderburn_degree.

Lemma Wedderburn_degree_gt0 : forall i, n_ i > 0.
Proof. by move=> i; rewrite lt0n mxrank_eq0; case: (socle_simple i). Qed.

Lemma degree_principal_comp : n_ principal_comp = 1%N.
Proof.
apply/eqP; rewrite eqn_leq Wedderburn_degree_gt0 -rank_principal_comp.
by rewrite mxrankS ?component_mx_id //; exact: socle_simple.
Qed.

Lemma rank_Wedderburn_subring : forall i, \rank (R_ i) = (n_ i ^ 2)%N.
Proof.
move=> i; apply/eqP; rewrite -{1}[i]regular_comp_refl.
have irrSi := socle_irr i.
by case/andP: (splitG irrSi) => _; rewrite rank_regular_comp.
Qed.

Lemma sum_Wedderburn_degree : (\sum_i n_ i ^ 2 = nG)%N.
Proof.
apply: etrans (eqnP gring_free).
rewrite -Wedderburn_sum (mxdirectP Wedderburn_direct) /=.
by apply: eq_bigr => i _; rewrite rank_Wedderburn_subring.
Qed.

Lemma Wedderburn_degree_abelian : abelian G -> forall i, n_ i = 1%N.
Proof. by move=> cGG i; exact: mxsimple_abelian_linear (socle_simple i). Qed.

Lemma linear_Wedderburn_comp : forall i, n_ i = 1%N -> (i :=: socle_base i)%MS.
Proof.
move=> i ni1; apply/eqmxP; rewrite andbC -mxrank_leqif_eq -/(n_ i).
  by rewrite -(mxrankMfree _ gring_free) -genmxE rank_Wedderburn_subring ni1.
exact: component_mx_id (socle_simple i).
Qed.

Lemma Wedderburn_subring_center : forall i, ('Z(R_ i) :=: mxvec (e_ i))%MS.
Proof.
move=> i; have [nz_e Re ideR idRe] := Wedderburn_is_id i.
have Ze: (mxvec (e_ i) <= 'Z(R_ i))%MS.
  rewrite sub_capmx [(_ <= _)%MS]Re.
  by apply/cent_mxP=> A R_A; rewrite ideR // idRe.
pose irrG := socle_irr i; set rG := socle_repr i in irrG.
pose E_G := enveloping_algebra_mx rG; have absG := splitG irrG.
apply/eqmxP; rewrite andbC -(geq_leqif (mxrank_leqif_eq Ze)).
have ->: \rank (mxvec (e_ i)) = (0 + 1)%N.
  by apply/eqP; rewrite eqn_leq rank_leq_row lt0n mxrank_eq0 mxvec_eq0.
rewrite -(mxrank_mul_ker _ (lin_mx (gring_op rG))) addnC leq_add //.
  rewrite leqn0 mxrank_eq0 -subsetmx0 -(ker_regular_comp_op irrG) capmxS //.
  by rewrite regular_comp_refl capmxSl.
apply: leq_trans (mxrankS _) (rank_leq_row (mxvec 1%:M)).
apply/memmx_subP=> Ar; case/subsetmxP=> a ->{Ar}.
rewrite mulmxA mul_rV_lin /=; set A := vec_mx _.
rewrite memmx1 (mx_abs_irr_cent_scalar absG) // -memmx_cent_envelop.
apply/cent_mxP=> Br; rewrite -(regular_comp_envelop irrG) regular_comp_refl.
case/subsetmxP=> b; move/(canRL mxvecK)=> ->{Br}; rewrite mulmxA mx_rV_lin /=.
set B := vec_mx _; have RiB: (B \in R_ i)%MS by rewrite vec_mxK subsetmxMl.
have sRiR: (R_ i <= R_G)%MS by rewrite -Wedderburn_sum (sumsmx_sup i).
have: (A \in 'Z(R_ i))%MS by rewrite vec_mxK subsetmxMl.
rewrite sub_capmx; case/andP=> RiA; move/cent_mxP=> cRiA.
by rewrite -!gring_opM ?(memmx_subP sRiR) 1?cRiA.
Qed.

Lemma Wedderburn_center :
  ('Z(R_G) :=: \matrix_(i < #|sG|) mxvec (e_ (enum_val i)))%MS.
Proof.
have:= mxdirect_sums_center Wedderburn_sum Wedderburn_direct Wedderburn_ideal.
move/eqmx_trans; apply; apply/eqmxP; apply/andP; split.
  apply/sumsmx_subP=> i _; rewrite Wedderburn_subring_center.
  by apply: (eq_row_sub (enum_rank i)); rewrite rowK enum_rankK.
apply/row_subP=> i; rewrite rowK -Wedderburn_subring_center.
by rewrite (sumsmx_sup (enum_val i)).
Qed.

Lemma Wedderburn_card : #|sG| = tG.
Proof.
rewrite -(eqnP classg_base_free) classg_base_center.
have:= mxdirect_sums_center Wedderburn_sum Wedderburn_direct Wedderburn_ideal.
move->; rewrite (mxdirectP _) /=; last first.
  apply/mxdirect_sumsP=> i _; apply/eqP; rewrite -subsetmx0.
  rewrite -{2}(mxdirect_sumsP Wedderburn_direct i) // capmxS ?capmxSl //=.
  by apply/sumsmx_subP=> j neji; rewrite (sumsmx_sup j) ?capmxSl.
rewrite -sum1_card; apply: eq_bigr => i _; apply/eqP.
rewrite Wedderburn_subring_center eqn_leq rank_leq_row lt0n mxrank_eq0.
by rewrite andbT mxvec_eq0; case: (Wedderburn_is_id i).
Qed.

End Regular.

Lemma card_linear_comp : forall (gT : finGroupType) (G : {group gT}),
    forall (sG : socleType (regular_repr G)),
    [char F]^'.-group G -> group_splitting_field G ->
  #|[set i : sG | Wedderburn_degree i == 1%N]| = #|G : G^`(1)|%g.
Proof.
move=> gT G sG F'G splitG; apply/eqP; set lin := fun i => _ == _.
apply: socle_exists (regular_repr (G / G^`(1))%G) _ _ => sGq; apply/eqP.
have [_ nG'G] := andP (der_normal 1 G); rewrite -card_quotient //.
have cGqGq: abelian (G / G^`(1))%g by exact: sub_der1_abelian.
have F'Gq: [char F]^'.-group (G / G^`(1))%g by exact: morphim_pgroup.
have splitGq: group_splitting_field (G / G^`(1))%G.
  exact: quotient_splitting_field. 
rewrite -(sum_Wedderburn_degree sGq) // -sum1dep_card.
pose rG (j : sGq) := morphim_repr (socle_repr j) nG'G.
have irrG: mx_irreducible (rG _).
  by move=> j; apply/morphim_mx_irr; exact: socle_irr.
rewrite (reindex (fun j => regular_comp sG (rG j))) /= -/lin.
  apply: eq_big => [j | j _]; last by rewrite Wedderburn_degree_abelian.
  have [_ lin_j _ _] := rsim_regular_comp sG F'G (irrG j).
  by rewrite /Wedderburn_degree -lin_j [\rank _]Wedderburn_degree_abelian.
have sG'k: G^`(1)%g \subset rker (socle_repr (val (_ : {i | lin i}))).
  by case=> i lin_i; rewrite rker_linear //=; exact/eqP.
pose h' u := regular_comp sGq (quo_repr (sG'k u) nG'G).
have irrGq: mx_irreducible (quo_repr (sG'k _) nG'G).
  by move=> u; apply/quo_mx_irr; exact: socle_irr.
exists (fun i => oapp h' (principal_comp sGq) (insub i)) => [j | i] lin_i.
  rewrite (insubT lin lin_i) /=; symmetry; apply/eqP; apply/socle_rsimP.
  apply: mx_rsim_trans (rsim_regular_comp sGq F'Gq (irrGq _)).
  have [g lin_g inj_g hom_g] := rsim_regular_comp sG F'G (irrG j).
  by exists g => // ?; case/morphimP=> x _ Gx ->; rewrite quo_repr_coset ?hom_g.
rewrite (insubT lin lin_i) /=; symmetry; apply/eqP; apply/socle_rsimP.
set u := exist _ _ _; apply: mx_rsim_trans (rsim_regular_comp sG F'G (irrG _)).
have [g lin_g inj_g hom_g] := rsim_regular_comp sGq F'Gq (irrGq u).
exists g => // x Gx; have:= hom_g (coset _ x).
by rewrite mem_morphim ?(subsetP nG'G) // quo_repr_coset // => ->.
Qed.

End GenRepr.

Implicit Arguments mxmoduleP [F gT G n rG m U].
Implicit Arguments envelop_mxP [F gT G n rG A].
Implicit Arguments hom_mxP [F gT G n rG m f W].
Implicit Arguments mx_Maeshke [F gT G n U].
Implicit Arguments rfix_mxP [F gT G n rG m W].
Implicit Arguments cyclic_mxP [F gT G n rG u v].
Implicit Arguments annihilator_mxP [F gT G n rG u A].
Implicit Arguments row_hom_mxP [F gT G n rG u v].
Implicit Arguments mxsimple_isoP [F gT G n rG U V].
Implicit Arguments socleP [F gT G n rG sG0 W W'].
Implicit Arguments centgmxP [F gT G n rG f].
Implicit Arguments rkerP [F gT G n rG x].
Implicit Arguments mx_abs_irrP [F gT G n rG].
Implicit Arguments socle_rsimP [F gT G n rG sG W1 W2].

Implicit Arguments val_submod_inj [F n U m].
Implicit Arguments val_factmod_inj [F n U m].
Prenex Implicits val_submod_inj val_factmod_inj.

(* This is Gorenstein, Lemma 2.6.3. *)
Lemma rfix_pgroup_char : forall (F : fieldType) (gT : finGroupType),
    forall (G : {group gT}) n (rG : mx_representation F G n),
  n > 0 -> [char F].-group G -> rfix_mx rG G != 0.
Proof.
move=> F gT G n; move: {2}_.+1 (ltnSn (n + #|G|)) => m.
elim: m => // m IHm in gT n G *; rewrite ltnS => le_nG_m rG n_gt0 charF_G.
apply/eqP=> Gregular; have irrG: mx_irreducible rG.
  apply/mx_irrP; split=> // U modU; rewrite -mxrank_eq0 -lt0n => Unz.
  rewrite /row_full eqn_leq rank_leq_col leqNgt; apply/negP=> ltUn. 
  have: rfix_mx (submod_repr modU) G != 0.
    by apply: IHm => //; apply: leq_trans le_nG_m; rewrite ltn_add2r.
  by rewrite -mxrank_eq0 (rfix_submod modU) // Gregular capmx0 linear0 mxrank0.
have{m le_nG_m IHm} faithfulG: mx_repr_faithful rG.
  apply/trivgP; apply/eqP; apply/idPn; set C := _ rG => ntC.
  suffices: rfix_mx (kquo_repr rG) (G / _)%g != 0.
    by rewrite -mxrank_eq0 rfix_quo Gregular mxrank0.
  apply: IHm (morphim_pgroup _ _) => //.
  by apply: leq_trans le_nG_m; rewrite ltn_add2l ltn_quotient // rstab_sub.
have{Gregular} ntG: G :!=: 1%g.
  apply: contraL n_gt0; move/eqP=> G1; rewrite -leqNgt -(mxrank1 F n).
  rewrite -(mxrank0 F n n) -Gregular mxrankS //; apply/rfix_mxP=> x.
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
have{irrG faithfulG cGz1} Urz1: rG z - 1%:M \in unitmx.
  apply: (mx_Schur irrG) cGz1 _; rewrite subr_eq0.
  move/implyP: (subsetP faithfulG z).
  by rewrite !inE Gz mul1mx -order_eq1 ozp -implybN neq_ltn orbC prime_gt1.
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
  qf_eval e subsetmx_form = (eval_mx e A <= eval_mx e B)%MS.
Proof.
move=> e; rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/idP=> [|sAB d]; last first.
  rewrite !eval_mxrank eval_col_mx -addsmxE; apply/implyP; move/eqP <-.
  by rewrite mxrank_leqif_sup ?addsmxSr // addsmx_sub sAB /=.
move/(_ (inord (\rank (eval_mx e (col_mx A B))))).
rewrite inordK ?ltnS ?rank_leq_col // !eval_mxrank eqxx /= eval_col_mx.
by rewrite -addsmxE mxrank_leqif_sup ?addsmxSr // addsmx_sub; case/andP.
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

Definition mxmodule_form (U : 'M[term]_n) :=
  \big[And/True]_(x \in G) subsetmx_form (mulmx_term U (mx_term (rG x))) U.

Lemma mxmodule_form_qf : forall U, qf_form (mxmodule_form U).
Proof.
move=> U; rewrite (morphAnd (@qf_form _)) ?big1 //= => x _.
by rewrite subsetmx_form_qf.
Qed.

Lemma eval_mxmodule : forall U e,
   qf_eval e (mxmodule_form U) = mxmodule rG (eval_mx e U).
Proof.
move=> U e; rewrite (morphAnd (qf_eval e)) //= big_andE /=.
apply/forallP/mxmoduleP=> Umod x; move/implyP: (Umod x);
  by rewrite eval_subsetmx eval_mulmx eval_mx_term.
Qed.

Definition mxnonsimple_form (U : 'M[term]_n) :=
  let V := vec_mx (row_var (n * n) 0) in
  let nzV := (~ mxrank_form 0 V)%T in
  let properVU := (subsetmx_form V U /\ ~ subsetmx_form U V)%T in
  (Exists_row_form (n * n) 0 (mxmodule_form V /\ nzV /\ properVU))%T.

Definition mxnonsimple (U : 'M_n) :=
  exists V : 'M_n, [&& mxmodule rG V, (V <= U)%MS, V != 0 & \rank V < \rank U].

Lemma not_mxnonsimple : forall U,
  mxmodule rG U -> U != 0 -> ~ mxnonsimple U -> mxsimple rG U.
Proof.
move=> U modU nzU nsimU; split=> // V [modV sVU] nzV.
apply/eqmxP; rewrite -mxrank_leqif_eq // eqn_leq mxrankS // leqNgt.
by apply/negP=> ltVU; case: nsimU; exists V; exact/and4P.
Qed.

Definition mxnonsimple_sat U :=
  GRing.sat (@row_env (n * n) [::]) (mxnonsimple_form (mx_term U)).

Lemma mxnonsimpleP : forall U,
  U != 0 -> reflect (mxnonsimple U) (mxnonsimple_sat U).
Proof.
rewrite /mxnonsimple_sat {1}/mxnonsimple_form; set Vt := vec_mx _ => /= U nzU.
pose nsim V := [&& mxmodule rG V, (V <= U)%MS, V != 0 & \rank V < \rank U].
set nsimUt := (_ /\ _)%T; have: qf_form nsimUt.
  by rewrite /= mxmodule_form_qf !mxrank_form_qf !subsetmx_form_qf.
move/GRing.qf_evalP; set qev := @GRing.qf_eval _ => qevP.
have qev_nsim: forall u, qev (row_env [:: u]) nsimUt = nsim n (vec_mx u).
  move=> u; rewrite /nsim -mxrank_eq0 /qev /= eval_mxmodule eval_mxrank.
  rewrite !eval_subsetmx eval_mx_term eval_vec_mx eval_row_var /=.
  do 2!bool_congr; apply: andb_id2l => sUV.
  by rewrite ltn_neqAle andbC !mxrank_leqif_sup.
have n2gt0: n ^ 2 > 0.
  by move: nzU; rewrite muln_gt0 -mxrank_eq0; case: posnP (U) => // ->.
apply: (iffP satP) => [|[V nsimV]].
  by case/Exists_rowP=> // v; move/qevP; rewrite qev_nsim; exists (vec_mx v).
apply/Exists_rowP=> //; exists (mxvec V); apply/qevP.
by rewrite qev_nsim mxvecK.
Qed.

Lemma dec_mxsimple_exists : forall U : 'M_n,
  mxmodule rG U -> U != 0 -> {V | mxsimple rG V & V <= U}%MS.
Proof.
move=> U; elim: {U}_.+1 {-2}U (ltnSn (\rank U)) => // m IHm U leUm modU nzU.
case: (mxnonsimpleP nzU) => [nsimU | simU]; last first.
  by exists U; first exact: not_mxnonsimple.
case: (xchooseP nsimU); move: (xchoose _) => W; case/and4P=> modW sWU nzW ltWU.
case: (IHm W) => // [|V simV sVW]; first exact: leq_trans ltWU _.
by exists V; last exact: subsetmx_trans sVW sWU.
Qed.

Lemma dec_mx_reducible_semisimple : forall U,
  mxmodule rG U -> mx_completely_reducible rG U -> mxsemisimple rG U.
Proof.
move=> U; elim: {U}_.+1 {-2}U (ltnSn (\rank U)) => // m IHm U leUm modU redU.
case: (eqVneq U 0) => [U0 | nzU].
  have{U0} U0: (\sum_(i < 0) 0 :=: U)%MS by rewrite big_ord0 U0.
  by apply: (intro_mxsemisimple U0); case.
have [V simV sVU] := dec_mxsimple_exists modU nzU; have [modV nzV _] := simV.
have [W modW defVW dxVW] := redU V modV sVU.
have [||I W_ /= simW defW _] := IHm W _ modW.
- rewrite ltnS in leUm; apply: leq_trans leUm.
  by rewrite -defVW (mxdirectP dxVW) /= -add1n leq_add2r lt0n mxrank_eq0.
- by apply: mx_reducibleS redU; rewrite // -defVW addsmxSr.
suffices defU: (\sum_i oapp W_ V i :=: U)%MS.
  by apply: (intro_mxsemisimple defU) => [] [|i] //=.
apply: eqmx_trans defVW; rewrite (bigD1 None) //=; apply/eqmxP.
case: (pickP I) => [i0 _ | I0].
  by rewrite (reindex some) ?addsmxS ?defW //; exists (odflt i0) => //; case.
rewrite big_pred0 //; last by case => //; move/I0.
by rewrite !addsmxS ?subset0mx // -defW big_pred0.
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

Section MapMatrixAlgebra.

Lemma map_mx_is_scalar : forall n (A : 'M_n), is_scalar_mx A^f = is_scalar_mx A.
Proof.
move=> n A; rewrite /is_scalar_mx; case: (insub _) => // i.
by rewrite mxE -(map_scalar_mx fRM) inj_eq //; exact: map_mx_inj.
Qed.

Lemma memmx_map : forall m n A (E : 'A_(m, n)), (A^f \in E^f)%MS = (A \in E)%MS.
Proof. by move=> m n A E; rewrite -map_mxvec subsetmx_map. Qed.

Lemma map_mulsmx : forall m1 m2 n (E1 : 'A_(m1, n)) (E2 : 'A_(m2, n)),
  ((E1 * E2)%MS^f :=: E1^f * E2^f)%MS.
Proof.
rewrite /mulsmx => m1 m2 n E1 E2; pose Rf (P Pf : 'A_n) := (P^f :=: Pf)%MS.
apply: (big_rel Rf) => [|P1 P1f P2 P2f ? ?|i _]; first by rewrite /Rf map_mx0.
  by apply: eqmx_trans (map_addsmx fRM _ _) _; exact: adds_eqmx.
apply/eqmxP; rewrite !map_genmx // !genmxE map_mxM //.
apply/rV_eqP=> u; congr (u <= _ *m _)%MS.
by apply: map_lin_mx => //= A; rewrite map_mxM // map_vec_mx map_row.
Qed.

Lemma map_cent_mx : forall m n (E : 'A_(m, n)), ('C(E)%MS)^f = 'C(E^f)%MS.
Proof.
move=> m n E; rewrite map_kermx //; congr (kermx _); apply: map_lin_mx => // A.
rewrite map_mxM //; congr (_ *m _); apply: map_lin_mx => //= B.
by rewrite map_mx_sub ? map_mxM.
Qed.

Lemma map_center_mx : forall m n (E : 'A_(m, n)), (('Z(E))^f :=: 'Z(E^f))%MS.
Proof. by move=> m n E; rewrite /center_mx -map_cent_mx; exact: map_capmx. Qed.

End MapMatrixAlgebra.

Section MapMinpoly.

Variable n' : nat.
Local Notation n := n'.+1.
Let mfRM := map_mxRM fRM n'.

Variable A : 'M[aF]_n.
Local Notation fp := (map_poly f).

Lemma map_powers_mx : forall e, (powers_mx A e)^f = powers_mx A^f e.
Proof.
move=> e; apply/row_matrixP=> i; rewrite -map_row !rowK map_mxvec.
by rewrite (ringM_exp (map_mxRM fRM _)).
Qed.

Lemma degree_mxminpoly_map : degree_mxminpoly A^f = degree_mxminpoly A.
Proof. by apply: eq_ex_minn => e; rewrite -map_powers_mx mxrank_map. Qed.

Lemma mxminpoly_map : mxminpoly A^f = fp (mxminpoly A).
Proof.
rewrite (ringM_sub (map_polyRM fRM)); congr (_ - _).
  by rewrite map_polyXn // degree_mxminpoly_map.
rewrite degree_mxminpoly_map -(ringM_exp (map_mxRM fRM _)).
apply/polyP=> i; rewrite coef_map // !coef_rVpoly degree_mxminpoly_map.
case/insub: i => [i|]; last by rewrite ringM_0.
by rewrite -map_powers_mx -map_pinvmx // -map_mxvec -map_mxM // mxE.
Qed.

Lemma map_horner_mx : forall p, (horner_mx A p)^f = horner_mx A^f (fp p).
Proof.
move=> p; rewrite ![horner_mx _ _]horner_poly size_map_poly // map_mx_sum //.
apply: eq_bigr => i _; rewrite coef_map // map_mxM // map_scalar_mx //.
by rewrite (ringM_exp mfRM).
Qed.

End MapMinpoly.

Variables (gT : finGroupType) (G : {group gT}).

Section OneRepresentation.

Variables (n : nat) (rG : mx_representation aF G n).

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

Lemma map_rfix_mx : forall H, (rfix_mx rG H)^f = rfix_mx rGf H.
Proof.
move=> H; rewrite map_kermx //; congr (kermx _); apply: map_lin1_mx => //= v.
rewrite map_mxvec (map_mxM fRM); congr (mxvec (_ *m _)); last first.
  by apply: map_lin1_mx => //= u; rewrite (map_mxM fRM) map_vec_mx.
apply/row_matrixP=> i.
by rewrite -map_row !rowK map_mxvec (map_mx_sub fRM) map_mx1.
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

Lemma mxmodule_map : forall m (U : 'M_(m, n)), mxmodule rGf U^f = mxmodule rG U.
Proof. by move=> m U; rewrite /mxmodule rstabs_map. Qed.

Lemma mxsimple_map : forall U : 'M_n, mxsimple rGf U^f -> mxsimple rG U.
Proof.
move=> U []; rewrite map_mx_eq0 // mxmodule_map // => modU nzU minU.
split=> // V modV sVU nzV; apply/eqmxP; rewrite sVU -(subsetmx_map fRM).
by rewrite (minU V^f) //= ?mxmodule_map // ?map_mx_eq0 // subsetmx_map.
Qed.

Lemma mx_irr_map : mx_irreducible rGf -> mx_irreducible rG.
Proof. by move=> irrGf; apply: mxsimple_map; rewrite map_mx1. Qed.

Lemma rker_map : rker rGf = rker rG.
Proof. by rewrite /rker -rstab_map map_mx1. Qed.

Lemma map_mx_repr_faithful : mx_repr_faithful rGf = mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_map. Qed.

Lemma map_mx_abs_irr :
  mx_absolutely_irreducible rGf = mx_absolutely_irreducible rG. 
Proof.
by rewrite /mx_absolutely_irreducible -map_enveloping_algebra_mx row_full_map.
Qed.

End OneRepresentation.

Lemma mx_rsim_map : forall n1 n2 rG1 rG2,
  @mx_rsim _ _ G n1 rG1 n2 rG2 -> mx_rsim (map_repr rG1) (map_repr rG2).
Proof.
move=> n1 n2 rG1 rG2 [g eqn12 inj_g hom_g].
by exists g^f => // [|x Gx]; rewrite ?row_free_map // -!map_mxM ?hom_g.
Qed.

Lemma map_regular_repr : map_repr (regular_repr aF G) =1 regular_repr rF G.
Proof. by move=> x; apply/matrixP=> i j; rewrite !mxE ringM_nat. Qed.

Lemma map_subfact_repr : forall n (rG : mx_representation aF G n) rGf U V,
    forall (modU : mxmodule rG U) (modV : mxmodule rG V),
    forall (modUf : mxmodule rGf U^f) (modVf : mxmodule rGf V^f),
  map_repr rG =1 rGf ->
  mx_rsim (map_repr (subfact_repr modU modV)) (subfact_repr modUf modVf).
Proof.
move=> n rG rGf U V modU modV modUf modVf def_rGf; set VU := <<_>>%MS.
pose valUV := val_factmod (val_submod (1%:M : 'M[aF]_(\rank VU))).
have sUV_Uf: (valUV^f <= U^f + V^f)%MS.
  rewrite -map_addsmx // subsetmx_map //.
  apply: subsetmx_trans (proj_factmodS _ _).
  by rewrite val_factmodS val_submod1 genmxE.
exists (in_submod _ (in_factmod U^f valUV^f)) => [||x Gx].
- rewrite !genmxE -(mxrank_map fRM) map_mxM // (map_col_base fRM).
  by case: (\rank (cokermx U)) / (mxrank_map _ _); rewrite map_cokermx.
- rewrite -kermx_eq0 -subsetmx0; apply/rV_subP=> u.
  rewrite (sameP sub_kermxP eqP) subsetmx0 -val_submod_eq0.
  rewrite val_submodE -mulmxA -val_submodE in_submodK; last first.
    by rewrite genmxE -(in_factmod_addsK _ V^f) subsetmxMr.
  rewrite in_factmodE mulmxA -in_factmodE in_factmod_eq0.
  move/(subsetmxMr (in_factmod U 1%:M *m in_submod VU 1%:M)^f).
  rewrite -mulmxA -!map_mxM //; do 2!rewrite mulmxA -in_factmodE -in_submodE.
  rewrite val_factmodK val_submodK map_mx1 // mulmx1.
  have ->: in_factmod U U = 0 by apply/eqP; rewrite in_factmod_eq0.
  by rewrite linear0 map_mx0 // eqmx0 subsetmx0.
rewrite {1}in_submodE mulmxA -in_submodE -in_submodJ; last first.
  by rewrite genmxE -(in_factmod_addsK _ V^f) subsetmxMr.
congr (in_submod _ _); rewrite -in_factmodJ // in_factmodE mulmxA -in_factmodE.
apply/eqP; rewrite -subr_eq0 -def_rGf -!map_mxM // -linear_sub in_factmod_eq0.
rewrite -map_mx_sub // subsetmx_map // -in_factmod_eq0 linear_sub.
rewrite /= (in_factmodJ modU) // val_factmodK.
rewrite [valUV]val_factmodE mulmxA -val_factmodE val_factmodK.
rewrite -val_submodE in_submodK ?subrr //.
by rewrite mxmodule_trans ?subfact_module // val_submod1.
Qed.

Lemma map_regular_subseries : forall U i,
    forall modU : mx_subseries (regular_repr aF G) U,
    forall modUf : mx_subseries (regular_repr rF G) (map (fun M => M^f) U),
  mx_rsim (map_repr (subseries_repr i modU)) (subseries_repr i modUf).
Proof.
set mf := map _ => U i modU modUf; rewrite /subseries_repr.
do 2!move: (mx_subseries_module' _ _) (mx_subseries_module _ _).
have mf_i: forall V, nth 0^f (mf V) i = (V`_i)^f.
  move=> V; case: (ltnP i (size V)) => [ltiV | leVi]; first exact: nth_map.
  by rewrite !nth_default ?size_map.
rewrite -(map_mx0 fRM) mf_i (mf_i (0 :: U)) => modUi'f modUif modUi' modUi.
exact: map_subfact_repr map_regular_repr.
Qed.

Lemma extend_group_splitting_field :
  group_splitting_field aF G -> group_splitting_field rF G.
Proof.
move=> splitG n rG irrG.
have modU0: all ((mxmodule (regular_repr aF G)) #|G|) [::] by [].
apply: (mx_Schreier modU0 _) => // [[U [compU lastU _]]]; have [modU _]:= compU.
pose Uf := map ((map_mx f) _ _) U.
have{lastU} lastUf: (last 0 Uf :=: 1%:M)%MS.
  by rewrite -(map_mx0 fRM) -(map_mx1 fRM) last_map; exact/eqmx_map.
have modUf: mx_subseries (regular_repr rF G) Uf.
  rewrite /mx_subseries all_map; apply: etrans modU; apply: eq_all => Ui /=.
  rewrite -mxmodule_map; apply: eq_subset_r => x.
  by rewrite !inE map_regular_repr.
have absUf: forall i, i < size U ->
  mx_absolutely_irreducible (subseries_repr i modUf).
- move=> i lt_i_U; rewrite -(mx_rsim_abs_irr (map_regular_subseries i modU _)).
  rewrite map_mx_abs_irr; apply: splitG.
  by apply: mx_rsim_irr (mx_series_repr_irr compU lt_i_U); exact: subfact_eqmx.
have compUf: mx_composition_series (regular_repr rF G) Uf.
  split=> // i; rewrite size_map => ltiU.
  move/max_submodP: (mx_abs_irrW (absUf i ltiU)); apply.
  rewrite -{2}(map_mx0 fRM) -map_cons !(nth_map 0) ?leqW //.
  by rewrite subsetmx_map // ltmxW // (pathP _ (mx_series_lt compU)).
have [[i ltiU] simUi] := rsim_regular_series irrG compUf lastUf.
have{simUi} simUi: mx_rsim rG (subseries_repr i modUf).
  by apply: mx_rsim_trans simUi _; exact: subfact_eqmx.
by rewrite (mx_rsim_abs_irr simUi) absUf; rewrite size_map in ltiU.
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
Local Notation Ad := (powers_mx A d).
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
by rewrite -horner_mxK mx_inv_hornerK ?horner_mx_mem // (ringM_mul mxRM).
Qed.

Lemma mxval_genV : {morph mxval : x / genV x >-> invmx x}.
Proof.
move=> x; rewrite /mxval [pval _]poly_rV_K ?size_poly ?mx_inv_hornerK //.
pose m B : 'M[F]_(n * n) := lin_mx (mulmxr B); set B := mxval x.
case uB: (GRing.unit B); last by rewrite invr_out ?uB ?horner_mx_mem.
have defAd: Ad = Ad *m m B *m m B^-1.
  apply/row_matrixP=> i.
  by rewrite !row_mul mul_rV_lin /= mx_rV_lin /= mulmxK ?vec_mxK.
rewrite -[B^-1]mul1mx -(mul_vec_lin (mulmxr_linear _ _)) defAd subsetmxMr //.
rewrite -mxval_gen1 (subsetmx_trans (horner_mx_mem _ _)) // {1}defAd.
rewrite -(geq_leqif (mxrank_leqif_sup _)) ?mxrankM_maxl // -{}defAd.
apply/row_subP=> i; rewrite row_mul rowK mul_vec_lin /= -horner_mx_Xn.
by rewrite -[_ *m _](ringM_mul mxRM) horner_mx_mem.
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
move=> x; rewrite [mxval _]horner_rVpoly -memmx_cent_envelop vec_mxK.
rewrite {x}mulmx_sub //; apply/row_subP=> k.
rewrite rowK memmx_cent_envelop; apply/centgmxP => g Gg /=.
by rewrite !mulmxE commr_exp // /GRing.comm -mulmxE (centgmxP cGA).
Qed.

Lemma gen_mulVr : GRing.Field.axiom genV.
Proof.
move=> x; rewrite -(inj_eq mxval_inj) mxval0.
move/(mx_Schur irrG (mxval_centg x)) => u_x.
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
by rewrite mx_inv_hornerK ?horner_mx_mem // horner_mx_X.
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

Lemma non_linear_gen_reducible : d > 1 -> mxnonsimple (map_repr genRM rG) 1%:M.
Proof.
rewrite ltnNge mxminpoly_linear_is_scalar => Anscal.
pose Af := map_mx gen A; exists (kermx (Af - groot%:M)).
rewrite subsetmx1 kermx_centg_module /=; last first.
  apply/centgmxP=> z Gz; rewrite mulmx_subl mulmx_subr scalar_mxC.
  by rewrite -!map_mxM 1?(centgmxP cGA).
rewrite andbC mxrank_ker -subn_gt0 mxrank1 subKn ?rank_leq_row // lt0n.
rewrite mxrank_eq0 subr_eq0; case: eqP => [defAf | _].
  rewrite -(map_mx_is_scalar genRM) -/Af in Anscal.
  by case/is_scalar_mxP: Anscal; exists groot.
rewrite -mxrank_eq0 mxrank_ker subn_eq0 row_leq_rank.
apply/row_freeP=> [[XA' XAK]].
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

Lemma gen_dim_ex_proof : exists m, existsb B : 'rV_m, row_free (subbase B).
Proof. by exists 0%N; apply/existsP; exists 0. Qed.

Lemma gen_dim_ub_proof : forall m,
   (existsb B : 'rV_m, row_free (subbase B)) -> (m <= n)%N.
Proof.
move=> m; case/existsP=> B; move/eqnP=> def_md.
by rewrite (leq_trans _ (rank_leq_col (subbase B))) // def_md leq_pmulr.
Qed.

Definition gen_dim := ex_maxn gen_dim_ex_proof gen_dim_ub_proof.
Notation m := gen_dim.

Definition gen_base : 'rV_m := odflt 0 [pick B | row_free (subbase B)].
Definition base := subbase gen_base.

Lemma base_free : row_free base.
Proof.
rewrite /base /gen_base /m; case: pickP => //; case: ex_maxnP => m_max.
by case/existsP=> B Bfree _ no_free; rewrite no_free in Bfree.
Qed.

Lemma base_full : row_full base.
Proof.
rewrite /row_full (eqnP base_free) /m; case: ex_maxnP => m.
case/existsP=> /= B; move/eqnP=> Bfree m_max.
rewrite -Bfree eqn_leq rank_leq_col.
rewrite -{1}(mxrank1 F n) mxrankS //; apply/row_subP=> j; set u := row _ _.
move/implyP: {m_max}(m_max m.+1); rewrite ltnn implybF.
apply: contraR => nBj; apply/existsP.
exists (row_mx (const_mx j : 'M_1) B); rewrite -row_leq_rank.
pose Bj := Ad *m lin1_mx (mulmx u \o vec_mx).
have rBj: \rank Bj = d.
  apply/eqP; rewrite eqn_leq rank_leq_row -subn_eq0 -mxrank_ker mxrank_eq0 /=.
  apply/rowV0P=> v; move/sub_kermxP; rewrite mulmxA mul_rV_lin1 /=.
  rewrite -horner_rVpoly; pose x := inFA v; rewrite -/(mxval x).
  case: (eqVneq x 0) => [[] // | nzx].
  move/(congr1 (mulmx^~ (mxval x^-1))); rewrite mul0mx /= -mulmxA -mxvalM.
  rewrite divff // mxval1 mulmx1.
  by move/rowP; move/(_ j); move/eqP; rewrite !mxE !eqxx oner_eq0.
rewrite {1}mulSn -Bfree -{1}rBj {rBj} -mxrank_disjoint_sum.
  rewrite mxrankS // addsmx_sub -[m.+1]/(1 + m)%N; apply/andP; split.
    apply/row_subP=> k; rewrite row_mul mul_rV_lin1 /=.
    apply: eq_row_sub (mxvec_index (lshift _ 0) k)  _.
    by rewrite !rowK mxvecK mxvecE mxE row_mxEl mxE -row_mul mul1mx. 
  apply/row_subP=> ik; case/mxvec_indexP: ik => i k.
  apply: eq_row_sub (mxvec_index (rshift 1 i) k) _.
  by rewrite !rowK !mxvecE 2!mxE row_mxEr.
apply/eqP; apply/rowV0P=> v; rewrite sub_capmx; case/andP; case/subsetmxP=> w.
set x := inFA w; rewrite {Bj}mulmxA mul_rV_lin1 /= -horner_rVpoly -/(mxval x).
move: (eqVneq x 0) => [-> | nzx ->]; first by rewrite mxval0 mulmx0.
move/(subsetmxMr (mxval x^-1)); rewrite -mulmxA -mxvalM divff {nzx}//.
rewrite mxval1 mulmx1 => Bx'j.
rewrite (subsetmx_trans Bx'j) in nBj => {nBj Bx'j} //; apply/row_subP.
case/mxvec_indexP=> i k; rewrite row_mul rowK mxvecE mxE rowE -mulmxA.
have ->: A ^+ k *m mxval x^-1 = mxval (groot ^+ k / x).
  by rewrite mxvalM (ringM_exp mxvalRM) mxval_groot.
rewrite [mxval _]horner_rVpoly; move: {k u x}(val _) => u.
rewrite (mulmx_sum_row u) !linear_sum summx_sub //= => k _.
rewrite !linearZ scalemx_sub //= rowK mxvecK -rowE.
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
have b_w: (w <= base)%MS by rewrite subsetmx_full ?base_full.
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
  (U <= V -> in_gen U <= in_gen V)%MS.
Proof.
move=> m1 m2 U V sUV; apply/row_subP=> i; rewrite -in_gen_row.
case/subsetmxP: (row_subP sUV i) => u ->{i}.
rewrite mulmx_sum_row in_gen_sum summx_sub // => j _.
by rewrite in_genZ in_gen_row scalemx_sub ?row_sub.
Qed.

Lemma subsetmx_in_gen_eq : forall m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, n)),
  (V *m A <= V -> (in_gen U <= in_gen V) = (U <= V))%MS.
Proof.
move=> m1 m2 U V sVA_V; apply/idP/idP=> siUV; last exact: subsetmx_in_gen.
apply/row_subP=> i; rewrite -[row i U]in_genK in_gen_row.
case/subsetmxP: (row_subP siUV i) => u ->{i U siUV}.
rewrite mulmx_sum_row val_gen_sum summx_sub // => j _.
rewrite val_genZ val_gen_row in_genK rowE -mulmxA mulmx_sub //.
rewrite [mxval _]horner_poly mulmx_sumr summx_sub // => [[k _]] _ /=.
rewrite mulmxA mul_mx_scalar -scalemxAl scalemx_sub {u j}//.
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
by rewrite (centgmxP (mxval_centg _)).
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

Lemma gen_rfix_mx : (rfix_mx rGA G :=: in_gen (rfix_mx rG G))%MS.
Proof.
apply/eqmxP; apply/andP; split; last first.
  by apply/rfix_mxP=> g Gg; rewrite -in_genJ // (rfix_mxP G _).
rewrite -[rfix_mx rGA G]val_genK; apply: subsetmx_in_gen.
by apply/rfix_mxP=> g Gg; rewrite -val_genJ ?(rfix_mxP G _).
Qed.

Definition rowval_gen m1 U :=
  <<\matrix_ik
      mxvec (\matrix_(i < m1, k < d) (row i (val_gen U) *m A ^+ k)) 0 ik>>%MS.

Lemma subsetmx_rowval_gen : forall m1 m2 (U : 'M_(m1, n)) (V : 'M_(m2, m)),
  (U <= rowval_gen V)%MS = (in_gen U <= V)%MS.
Proof.
move=> m1 m2 U V; rewrite genmxE; apply/idP/idP=> sUV.
  apply: subsetmx_trans (subsetmx_in_gen sUV) _.
  apply/row_subP; case/mxvec_indexP=> i k; rewrite -in_gen_row rowK mxvecE mxE.
  rewrite -mxval_grootX -val_gen_row -val_genZ val_genK scalemx_sub //.
  exact: row_sub.
rewrite -[U]in_genK; case/subsetmxP: sUV => u ->{U}.
apply/row_subP=> i0; rewrite -val_gen_row row_mul; move: {i0 u}(row _ u) => u.
rewrite mulmx_sum_row val_gen_sum summx_sub // => i _.
rewrite val_genZ [mxval _]horner_rVpoly [_ *m Ad]mulmx_sum_row.
rewrite !linear_sum summx_sub // => k _.
rewrite !linearZ scalemx_sub {u}//= rowK mxvecK val_gen_row.
by apply: (eq_row_sub (mxvec_index i k)); rewrite rowK mxvecE mxE.
Qed.

Lemma rowval_genK : forall m1 (U : 'M_(m1, m)),
  (in_gen (rowval_gen U) :=: U)%MS.
Proof.
move=> m1 U; apply/eqmxP; rewrite -subsetmx_rowval_gen subsetmx_refl /=.
by rewrite -{1}[U]val_genK subsetmx_in_gen // subsetmx_rowval_gen val_genK.
Qed.

Lemma rowval_gen_stable : forall m1 (U : 'M_(m1, m)),
  (rowval_gen U *m A <= rowval_gen U)%MS.
Proof.
move=> m1 U; rewrite -[A]mxval_groot -{1}[_ U]in_genK -val_genZ.
by rewrite subsetmx_rowval_gen val_genK scalemx_sub // rowval_genK.
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

Lemma mxmodule_rowval_gen : forall m1 (U : 'M_(m1, m)),
  mxmodule rG (rowval_gen U) = mxmodule rGA U.
Proof. by move=> m1 U; rewrite /mxmodule rstabs_rowval_gen. Qed.

Lemma gen_mx_irr : mx_irreducible rGA.
Proof.
apply/mx_irrP; split=> [|U Umod nzU]; first exact: gen_dim_gt0.
rewrite -subset1mx -rowval_genK -subsetmx_rowval_gen subsetmx_full //.
case/mx_irrP: irrG => _; apply; first by rewrite mxmodule_rowval_gen.
rewrite -(inj_eq (can_inj in_genK)) in_gen0.
by rewrite -mxrank_eq0 rowval_genK mxrank_eq0.
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
Local Notation Ad := (powers_mx A d).

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

(* This should be [countMixin of FA by <:]*)
Definition gen_countMixin := (sub_countMixin (gen_subType irrG cGA)).
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

(* Classical splitting and closure field constructions provide convenient     *)
(* packaging for the pointwise construction.                                  *)
Section BuildSplittingField.

Implicit Type gT : finGroupType.
Implicit Type F : fieldType.

Import MatrixGenField.

Lemma group_splitting_field_exists : forall gT (G : {group gT}) F,
  classically {Fs : fieldType | group_splitting_field Fs G
                              & exists f : F -> Fs, GRing.morphism f}.
Proof.
move=> gT G F0 [] // nosplit; pose nG := #|G|; pose aG F := regular_repr F G.
pose m := nG.+1; pose F := F0; pose U : seq 'M[F]_nG := [::].
suffices: size U + m <= nG by rewrite ltnn.
have: mx_subseries (aG F) U /\ path ltmx 0 U by [].
pose f : F0 -> F := id; have: GRing.morphism f by [].
elim: m F U f => [|m IHm] F U f fM [modU ltU].
  by rewrite addn0 (leq_trans (max_size_mx_series ltU)) ?rank_leq_row.
rewrite addnS ltnNge -implybF; apply/implyP=> le_nG_Um; apply nosplit.
exists F; last by [exists f]; case=> [|n] rG irrG; first by case/mx_irrP: irrG.
apply/idPn=> nabsG; pose cG := ('C(enveloping_algebra_mx rG))%MS.
have{nabsG} [A]: exists2 A, (A \in cG)%MS & ~~ is_scalar_mx A.
  apply/has_non_scalar_mxP; rewrite ?scalar_mx_cent // ltnNge.
  by apply: contra nabsG; exact: cent_mx_scalar_abs_irr.
rewrite {cG}memmx_cent_envelop -mxminpoly_linear_is_scalar -ltnNge => cGA.
move/(non_linear_gen_reducible irrG cGA); set F' := gen_fieldType _ _.
move: (gen _ _ : F -> F') (genRM _ _) => f' f'M.
move: {A cGA}F' f' {f'M}(f'M : GRing.morphism f') => F' f' f'M.
set rG' := map_repr _ rG => irrG'; case: not_false.
pose U' := map (fun Ui => map_mx f' Ui) U.
have modU': mx_subseries (aG F') U'.
  apply: etrans modU; rewrite /mx_subseries all_map; apply: eq_all => Ui.
  rewrite -(mxmodule_map f'M); apply: eq_subset_r => x.
  by rewrite !inE map_regular_repr.
apply: (mx_Schreier modU ltU) => [[V [compV lastV sUV]]].
have{lastV} [] := rsim_regular_series irrG compV lastV.
have{sUV} defV: V = U.
  apply/eqP; rewrite eq_sym -(geq_leqif (size_subseq_leqif sUV)).
  rewrite -(leq_add2r m); apply: leq_trans le_nG_Um.
  by apply: IHm fM _; rewrite (mx_series_lt compV); case compV.
rewrite {V}defV in compV * => i rsimVi.
apply: (mx_Schreier modU') => [|[V' [compV' _ sUV']]].
  rewrite {modU' compV modU i le_nG_Um rsimVi}/U' -(map_mx0 f'M).
  by apply: etrans ltU; elim: U 0 => //= Ui U IHU Ui'; rewrite IHU ltmx_map.
have{sUV'} defV': V' = U'; last rewrite {V'}defV' in compV'.
  apply/eqP; rewrite eq_sym -(geq_leqif (size_subseq_leqif sUV')) size_map.
  rewrite -(leq_add2r m); apply: leq_trans le_nG_Um.
  apply: IHm (comp_ringM f'M fM) _.
  by rewrite (mx_series_lt compV'); case compV'.
suffices{irrG'}: mx_irreducible rG' by case/mxsimpleP=> _ _ [].
have ltiU': i < size U' by rewrite size_map.
apply: mx_rsim_irr (mx_rsim_sym _ ) (mx_series_repr_irr compV' ltiU').
apply: mx_rsim_trans (mx_rsim_map f'M rsimVi) _; exact: map_regular_subseries.
Qed.

Lemma group_closure_field_exists : forall gT F,
  classically {Fs : fieldType | group_closure_field Fs gT
                              & exists f : F -> Fs, GRing.morphism f}.
Proof.
move=> gT F; set n := #|{group gT}|.
suffices: classically {Fs : fieldType
   | forall G : {group gT}, enum_rank G < n -> group_splitting_field Fs G
   & exists f : F -> Fs, GRing.morphism f}.
- apply: classic_bind => [[Fs splitFs morphFs]] _ -> //; exists Fs => // G.
  exact: splitFs.
elim: (n) => [|i IHi]; first by move=> _ -> //; exists F => //; exists id.
apply: classic_bind IHi => [[F' splitF' [f fM]]].
case: (ltnP i n) => [lt_i_n | le_n_i]; last first.
  move=> _ -> //; exists F' => [G _ | ]; last by exists f.
  apply: splitF'; exact: leq_trans le_n_i.
  have:= @group_splitting_field_exists _ (enum_val (Ordinal lt_i_n)) F'.
apply: classic_bind => [[Fs splitFs [f' f'M]]] _ -> //.
exists Fs => [G | ]; last by exists (f' \o f); exact: comp_ringM.
rewrite ltnS leq_eqVlt -{1}[i]/(val (Ordinal lt_i_n)) val_eqE.
case/predU1P=> [defG | ltGi]; first by rewrite -[G]enum_rankK defG.
by apply: (extend_group_splitting_field f'M); exact: splitF'.
Qed.

End BuildSplittingField.

(* Special results for representations on a finite field. In this case, the   *)
(* representation is equivalent to a morphism into the general linear group   *)
(* 'GL_n[F]. It is furthermore equivalent to a group action on the finite     *)
(* additive group of the corresponding row space 'rV_n. In addition, row      *)
(* spaces of matrices in 'M[F]_n correspond to subgroups of that vector group *)
(* (this is only surjective when F is a prime field 'F_p), with moduleules    *)
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

Definition rowg m (A : 'M[F]_(m, n)) : {set rVn} := [set u | u <= A]%MS.

Lemma mem_rowg : forall m A v, (v \in @rowg m A) = (v <= A)%MS.
Proof. by move=> m A v; rewrite inE. Qed.

Lemma rowg_group_set : forall m A, group_set (@rowg m A).
Proof.
move=> m A; apply/group_setP.
by split=> [|u v]; rewrite !inE ?subset0mx //; exact: addmx_sub.
Qed.
Canonical Structure rowg_group m A := Group (@rowg_group_set m A).

Lemma rowg_stable : forall m (A : 'M_(m, n)), [acts setT, on rowg A | 'Zm].
Proof.
by move=> m A; apply/actsP=> a _ v; rewrite !inE eqmx_scale // -unitfE (valP a).
Qed.

Lemma rowgS : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (rowg A \subset rowg B) = (A <= B)%MS.
Proof.
move=> m1 m2 A B; apply/subsetP/idP=> sAB => [| u].
  by apply/row_subP=> i; move/(_ (row i A)): sAB; rewrite !inE row_sub => ->.
by rewrite !inE => suA; exact: subsetmx_trans sAB.
Qed.

Lemma eq_rowg : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  (A :=: B)%MS -> rowg A = rowg B.
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

Definition rowg_mx (L : {set rVn}) := <<\matrix_(i < #|L|) enum_val i>>%MS.

Lemma rowgK : forall m (A : 'M_(m, n)), (rowg_mx (rowg A) :=: A)%MS.
Proof.
move=> m A; apply/eqmxP; rewrite !genmxE; apply/andP; split.
  by apply/row_subP=> i; rewrite rowK; have:= enum_valP i; rewrite /= inE.
apply/row_subP=> i; set v := row i A.
have Av: v \in rowg A by rewrite inE row_sub.
by rewrite (eq_row_sub (enum_rank_in Av v)) // rowK enum_rankK_in.
Qed.

Lemma rowg_mxS : forall L M : {set 'rV[F]_n},
  L \subset M -> (rowg_mx L <= rowg_mx M)%MS.
Proof.
move=> L M; move/subsetP=> sLM; rewrite !genmxE; apply/row_subP=> i.
rewrite rowK; move: (enum_val i) (sLM _ (enum_valP i)) => v Mv.
by rewrite (eq_row_sub (enum_rank_in Mv v)) // rowK enum_rankK_in.
Qed.

Lemma sub_rowg_mx : forall L : {set rVn}, L \subset rowg (rowg_mx L).
Proof.
move=> L; apply/subsetP=> v Lv; rewrite inE genmxE.
by rewrite (eq_row_sub (enum_rank_in Lv v)) // rowK enum_rankK_in.
Qed.

Lemma stable_rowg_mxK : forall L : {group rVn},
  [acts setT, on L | 'Zm] -> rowg (rowg_mx L) = L.
Proof.
move=> L linL; apply/eqP; rewrite eqEsubset sub_rowg_mx andbT.
apply/subsetP => v; rewrite inE genmxE; case/subsetmxP=> u ->{v}.
rewrite mulmx_sum_row group_prod // => i _.
rewrite rowK; move: (enum_val i) (enum_valP i) => v Lv.
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
  rowg (A :&: B)%MS = rowg A :&: rowg B.
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
  rowg (A + B)%MS = (rowg A * rowg B)%g.
Proof.
move=> m1 m2 A B; apply/eqP; rewrite eq_sym eqEcard mulG_subG /= !rowgS.
rewrite addsmxSl addsmxSr -(@leq_pmul2r #|rowg A :&: rowg B|) ?cardG_gt0 //=.
by rewrite -mul_cardG -rowgI !card_rowg -!expn_add mxrank_sum_cap.
Qed.

(* An alternative proof, which avoids the counting argument.
   It's outcommented because the mem_mulg rewrite takes forever to execute.
Lemma rowgD' : forall m1 m2 (A : 'M_(m1, n)) (B : 'M_(m2, n)),
  rowg (A + B)%MS = (rowg A * rowg B)%g.
Proof.
move=> m1 m2 A B; apply/eqP; rewrite eq_sym eqEsubset mulG_subG /= !rowgS.
rewrite addsmxSl addsmxSr; apply/subsetP=> u; rewrite !inE.
by case/sub_addsmxP=> v suvA svB; rewrite -(mulgKV v u) mem_mulg ?inE.
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

Lemma acts_rowg : forall A : 'M_n, [acts G, on rowg A | 'MR rG] = mxmodule rG A.
Proof. by move=> A; rewrite astabs_rowg_repr. Qed.

Lemma astab_setT_repr : 'C(setT | 'MR rG) = rker rG.
Proof. by rewrite -rowg1 astab_rowg_repr. Qed.

Lemma mx_repr_action_faithful :
  [faithful G, on setT | 'MR rG] = mx_repr_faithful rG.
Proof.
rewrite /faithful astab_setT_repr (setIidPr _) //.
by apply/subsetP=> x; case/setIdP.
Qed.

Lemma afix_repr : 'Fix_('MR rG)(G) = rowg (rfix_mx rG G).
Proof.
apply/setP=> /= u; rewrite !inE.
apply/subsetP/rfix_mxP=> cHu x Hx;
  by move/(_ x Hx): cHu; rewrite !inE /=; move/eqP; rewrite mx_repr_actE.
Qed.

Lemma gacent_repr : 'C_(| 'MR rG)(G) = rowg (rfix_mx rG G).
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
move=> p_pr; apply/abelemP=> //; rewrite zmod_abelian.
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
  (rowg_mx L <= rowg_mx M)%MS = (L \subset M).
Proof.
move=> L M; apply/idP/idP; last exact: rowg_mxS.
by rewrite -rowgS rowg_mxK; apply: subset_trans; exact: sub_rowg_mx.
Qed.

End FpRow.

Variables (p : nat) (gT : finGroupType) (E : {group gT}).
Hypotheses (abelE : p.-abelem E) (ntE : E :!=: 1%g).

Let pE : p.-group E := abelem_pgroup abelE.
Let p_pr : prime p. Proof. by have [] := pgroup_pdiv pE ntE. Qed.

Local Notation n' := (abelem_dim' (gval E)).
Local Notation n := n'.+1.
Local Notation rVn := 'rV['F_p](gval E).

Lemma dim_abelemE : n = logn p #|E|.
Proof.
rewrite /n'; have [_ _ [k ->]] :=  pgroup_pdiv pE ntE.
by rewrite /pdiv primes_exp ?primes_prime // pfactorK.
Qed.

Lemma card_abelem_rV : #|rVn| = #|E|.
Proof.
by rewrite dim_abelemE card_matrix mul1n card_Fp // -p_part part_pnat_id.
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
  apply/mx_irrP; split=> // U; rewrite /mxmodule rstabs_abelem //.
  rewrite subsetI subxx /= -trivg_rowg.
  rewrite -(inj_eq rVabelem_minj) morphim1; set L := _ @* _ U => nLG ntL. 
  by rewrite -subset1mx -rowgS -rVabelemS -/L [L]minE ?ntL /=.
rewrite ntE; split=> // L; case/andP=> ntL nLG sLE; apply/eqP.
rewrite eqEsubset sLE -im_rVabelem sub_rVabelem_im //= -rowg_mxSK //.
move/setIidPl: nLG; rewrite -rstabs_abelem_rowg_mx //.
set U := rowg_mx _ => Umod; rewrite subsetmx_full //.
case/mx_irrP: irrG => _ -> //; first by rewrite /mxmodule Umod.
apply: contra ntL; rewrite rowg_mx_eq0 !(sameP eqP trivgP).
by rewrite sub_abelem_rV_im // morphim1.
Qed.

Lemma rfix_abelem : (rfix_mx rG G :=: rowg_mx (ErV @* 'C_E(G)%g))%MS.
Proof.
apply/eqmxP; apply/andP; split.
  rewrite -rowgS rowg_mxK -sub_rVabelem_im // subsetI sub_rVabelem /=.
  apply/centsP=> y; case/morphimP=> v _; rewrite inE => cGv ->{y} x Gx.
  by apply/commgP; apply/conjg_fixP; rewrite /= -rVabelemJ // (rfix_mxP G _).
rewrite genmxE; apply/rfix_mxP=> x Gx.
apply/row_matrixP=> i; rewrite row_mul rowK.
case/morphimP: (enum_valP i) => z Ez; case/setIP=> _ cGz ->.
by rewrite -abelem_rV_J // conjgE (centP cGz) ?mulKg.
Qed.

Lemma rker_abelem : rker rG = 'C_G(E).
Proof. by rewrite /rker rstab_abelem rowg1 im_rVabelem. Qed.

Lemma abelem_repr_faithful : 'C_G(E) = 1%g -> mx_repr_faithful rG.
Proof. by rewrite /mx_repr_faithful rker_abelem => ->. Qed.
  
End AbelemRepr.
