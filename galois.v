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
 forall u v, (mxvec u <= K -> mxvec v <= K -> mxvec (u *m v) <= K)%MS.
move => K.
case/and3P => _ _.
move/forallP => Kfield u v.
do 2 (case/subsetmxP => ?; move/(canRL mxvecK)=> ->).
rewrite !mulmx_sum_row !linear_sum /=.
apply: subsetmx_sum => j _.
rewrite linearZ mulmx_suml !linear_sum /=.
apply: subsetmx_sum => i _.
rewrite !linearZ /= -scalemxAl linearZ /=.
do 2 apply: subsetmx_scale.
by move/forallP : (Kfield i).
Qed.

Lemma Lsubfield : subfield L.
Proof.
apply/and3P;split=>//.
do 2!apply/forallP => ?;
by apply: LmulClosed; rewrite vec_mxK; apply row_sub.
Qed. 

Lemma subFisFP : forall v, reflect (exists c, v = c%:M) (mxvec v <= F)%MS.
by move=> v; rewrite genmxE; apply: (iffP sub_rVP); move=> [x Jx]; exists x;
 move: Jx; rewrite -linearZ scalemx1 /=; [apply (can_inj mxvecK)|move ->].
Qed.

Lemma FisSubF : forall c, (mxvec (c%:M) <= F)%MS.
by move=> c; apply/subFisFP; exists c.
Qed.

Hint Resolve FisSubF.

Lemma Fsubfield : subfield F.
Proof.
apply/and3P;split=>//.
apply/forallP => i.
apply/forallP => j.
move: (row_sub i F) (row_sub j F).
rewrite -{1}(vec_mxK (row i F)).
rewrite -{1}(vec_mxK (row j F)).
do 2!move/subFisFP => [? ->].
by rewrite -scalar_mxM.
Qed.

(* In applications we will require that (subfield E) and (subfield K). *)
Definition FieldAutomorphism (f : 'M[F0]_(n*n)) (E K:subspace) : bool :=
  (* the image of E is E *)
[&& (E *m f == E)%MS
  (* K is fixed *)
  , (K *m f == K)
  (* Products are preserved *)
  , (forallb i, forallb j, 
      mxvec (vec_mx (row i E *m f) *m vec_mx (row j E *m f)) == 
      mxvec (vec_mx (row i E) *m vec_mx (row j E)) *m f)
  (* the image on E^C is fixed (for canonicity purposes)*)
  & ((E^C)%MS *m f == (E^C)%MS)
].

Lemma idAutomorphism : forall E K, FieldAutomorphism 1 E K.
Proof.
move => E K.
by apply/and4P; split; do ? (apply/forallP => i;apply/forallP => j);
 rewrite ?mulmx1 //; apply/andP.
Qed.

Lemma AutomorphsimEE_id : forall E f, FieldAutomorphism f E E -> f = 1%:M.
Proof.
move => E f.
case/and4P => _.
move/eqP => Hf1 _.
move/eqP => Hf2.
apply/row_matrixP => i.
rewrite row1 rowE.
have: (delta_mx (0:'I_1) i <= E + E^C)%MS.
 apply subsetmx_full; apply sumsmx_compl_full.
case/sub_sumsmxP => x.
rewrite {-1}(_:delta_mx 0 i = (delta_mx 0 i - x) + x); 
 last by rewrite GRing.Theory.subrK.
do 2!move/subsetmxP => [? ->].
by rewrite mulmx_addl -2!mulmxA Hf1 Hf2.
Qed.
