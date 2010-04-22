(* Import some random set of files *)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import choice fintype finfun bigops ssralg poly.
Require Import zmodp matrix mxrepresentation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Local Scope ring_scope.

Section Galois.

Variable F0 : fieldType.
Variable n' : nat.
Local Notation n := n'.+1.

(* L is a subspace of 'M[F]_n, represented as a row Matrix *)
Local Notation subspace := 'M[F0]_(n*n,n*n).
(* F' is F as a subspace, which is represented by the identity matrix *)
Let F : subspace := <<mxvec 1>>%MS.
Variable L : subspace.
(* L contains F *)
Hypothesis FinL : (F <= L)%MS.
(* L is closed under multiplication *)
Hypothesis LmulClosed :  
 (forall u v, mxvec u <= L -> mxvec v <= L -> mxvec (u *m v) <= L)%MS.
(* Mutiplication in L is commutative *)
Hypothesis Lcommute :
 (forall u v, mxvec u <= L -> mxvec v <= L -> u * v == v * u)%MS.
(* Every non-zero matrix in L is invertable *)
Hypothesis Linvertable :
 (forall u, mxvec u <= L -> \det u != 0)%MS.
(* Hypothesis Lcanonical : (<<L>> == L)%MS. *)

(* A subfield is a linear subspace of L that is closed under multiplication and contains 1 *)
Definition subfield (K : subspace) : bool :=
 [&& (K <= L)%MS
 ,(F <= K)%MS 
 & (forallb i, forallb j, mxvec (vec_mx (row i K) *m vec_mx (row j K)) <= K)%MS]
 (* && (<<f>> == f)%MS *).

Lemma subfieldMult : forall K, subfield K -> 
 forall u v, (mxvec v <= K -> mxvec u <= K -> mxvec (u *m v) <= K)%MS.
move => K.
move/and3P => [_ _ Kfield] u v.
move/subsetmxP => [u' Hu].
move/subsetmxP => [v' Hv].
move: Hu Hv.
rewrite !mulmx_sum_row.
move=> Hu Hv.
move: (canRL mxvecK Hu) (canRL mxvecK Hv).
clear Hu Hv.
rewrite !linear_sum.
move=> -> ->.
(* RESUME WORK HERE *)



Lemma Lsubfield : subfield L.
apply/and3P;split=>//.
apply/forallP => i.
apply/forallP => j.
apply (@LmulClosed (vec_mx (row i L)) (vec_mx (row j L))); 
rewrite vec_mxK; apply row_sub.
Qed. 

Lemma subFisFP : forall v, reflect (exists c, v = c%:M) (mxvec v <= F)%MS.
Proof.
move=> v.
have: (F:=:mxvec 1)%MS by apply: genmxE.
intros [_ HF1].
move:(HF1 _ (mxvec v)).
intros [_ ->].
clear HF1.
apply: (iffP sub_rVP);move=> [x Jx]; exists x; move: Jx; rewrite -linearZ.
 move=>Hv.
 rewrite (can_inj mxvecK Hv).
 by apply scalemx1.
move=> ->.
by rewrite scalemx1.
Qed.

Lemma FisSubF : forall c, (mxvec (c%:M) <= F)%MS.
Proof.
intros c.
apply/subFisFP.
by exists c.
Qed.

Hint Resolve FisSubF.

Lemma Fsubfield : subfield F.
apply/and3P;split=>//.
apply/forallP => i.
apply/forallP => j.
move: (row_sub i F) (row_sub j F).
rewrite -{1}(vec_mxK (row i F)).
rewrite -{1}(vec_mxK (row j F)).
move/subFisFP => [c ->].
move/subFisFP => [d ->].
by rewrite -scalar_mxM.
Qed.

(* In applications we will require that (subfield K). *)
Definition FieldAutomorphism (f : 'M[F0]_(n*n)) (K:subspace) : bool :=
  (* the image of L is L *)
  (L *m f == L)%MS
  (* K is fixed *)
&& (K *m f == K)
  (* Products are preserved *)
&& (forallb i, forallb j, 
     mxvec (vec_mx (row i L *m f) *m vec_mx (row j L *m f)) == 
     mxvec (vec_mx (row i L) *m vec_mx (row j L)) *m f)
  (* the image on L^C is fixed (for canonicity purposes)*)
&& ((L^C)%MS *m f == (L^C)%MS).

