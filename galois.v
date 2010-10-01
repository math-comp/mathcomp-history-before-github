(* Import some random set of files *)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import choice fintype finfun bigop ssralg poly.
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
Local Notation subspace := 'M[F0]_(n * n, n * n).
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
 forall u, (mxvec u <= L)%MS -> unitmx u.
(* Hypothesis Lcanonical : (<<L>> == L)%MS. *)

(* A subfield is a linear subspace of L that is closed under multiplication and contains 1 *)
Definition subfield (K : subspace) : bool :=
 [&& (K <= L)%MS
 ,(F <= K)%MS 
 & (forallb i, forallb j, mxvec (vec_mx (row i K) *m vec_mx (row j K)) <= K)%MS]
 (* && (<<f>> == f)%MS *).

Lemma subfieldMult : forall K, subfield K -> 
 forall u v, (mxvec u <= K -> mxvec v <= K -> mxvec (u *m v) <= K)%MS.
Proof.
move => K.
case/and3P => _ _.
move/forallP => Kfield u v.
do 2 (case/submxP => ?; move/(canRL mxvecK)=> ->).
rewrite !mulmx_sum_row !linear_sum /=.
apply: submx_sum => j _.
rewrite linearZ mulmx_suml !linear_sum /=.
apply: submx_sum => i _.
rewrite !linearZ /= -scalemxAl linearZ /=.
do 2 apply: submx_scale.
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
Definition FieldAutomorphism (f : 'M[F0]_(n * n)) (E K:subspace) : bool :=
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

Lemma AutomorphMul : forall E K f, FieldAutomorphism f E K -> 
forall u v, (u <= E)%MS -> (v <= E)%MS -> 
 mxvec (vec_mx (u *m f) *m vec_mx (v *m f)) = 
 mxvec (vec_mx u *m vec_mx v) *m f.
Proof.
move => E K f.
case/and4P => _ _.
move/forallP => fmult _ u v.
do 2 (case/submxP => ? ->).
rewrite 2![_ *m E]mulmx_sum_row /=.
rewrite !mulmx_suml !linear_sum !mulmx_suml /=.
apply: eq_bigr => j _.
rewrite !mulmx_suml !linear_sum !mulmx_suml /=.
apply: eq_bigr => i _.
rewrite !linearZ /= -!scalemxAl !linearZ /=.
rewrite -scalemxAl linearZ /=.
move/forallP : (fmult i).
move/(_ j).
move/eqP => ->.
by rewrite scalemxAl.
Qed.

Lemma idAutomorphism : forall E K, FieldAutomorphism 1 E K.
Proof.
move => E K.
by apply/and4P; split; do ? (apply/forallP => i;apply/forallP => j);
 rewrite ?mulmx1 //; apply/andP.
Qed.

Lemma compAutomorphism : forall E K f g, 
 FieldAutomorphism f E K ->  FieldAutomorphism g E K ->
 FieldAutomorphism (f *m g) E K.
Proof.
move => E K f g Ff Fg.
case/and4P: (Ff); move/eqmxP => Hf1; move/eqP => Hf2 _; move/eqP => Hf4.
case/and4P: (Fg); move/eqmxP => Hg1; move/eqP => Hg2 _; move/eqP => Hg4.
apply/and4P; split; do 2? apply/forallP => ?; 
 rewrite ?mulmxA ?Hf2 ?Hg2 ?Hf4 ?Hg4 //.
 by apply/eqmxP; apply (fun x => eqmx_trans x Hg1); apply eqmxMr.
by rewrite (AutomorphMul Fg) -?Hf1 ?(AutomorphMul Ff) //; 
 do ? apply submxMr; apply: row_sub.
Qed.

Lemma AutomorphismIsUnit : forall E K f, 
 FieldAutomorphism f E K -> f \in unitmx.
Proof.
move => E K f.
case/and4P.
move/eqmxP => Hf1 _ _.
move/eqP => Hf2.
rewrite -row_full_unit -sub1mx.
have H: (row_full (E + E^C)) by apply: sumsmx_compl_full.
rewrite -(eqmxMfull f H) sumsmxMr.
rewrite -sub1mx in H.
apply: (submx_trans H).
by apply: sumsmxS; rewrite ?Hf1 ?Hf2.
Qed.

Lemma invAutomorphism : forall E K f,
 FieldAutomorphism f E K -> FieldAutomorphism (invmx f) E K.
Proof.
move => E K f Hf.
case/and4P: (Hf).
move/eqmxP => Hf1.
move/eqP => Hf2.
move/forallP => Hf3.
move/eqP => Hf4.
apply/and4P.
move: (AutomorphismIsUnit Hf) => Uf.
have HE : (E *m invmx f :=: E)%MS.
 rewrite -{2}(mulmxK Uf E).
 apply: eqmxMr.
 by apply eqmx_sym.
split.
- by apply/eqmxP.
- by apply/eqP; by rewrite -{2}(mulmxK Uf K) Hf2.
- apply/forallP => i.
  apply/forallP => j.
  rewrite -{2}(mulmxKV Uf (row i E)).
  rewrite -{2}(mulmxKV Uf (row j E)).
  rewrite (AutomorphMul Hf) ?mulmxK // -HE;
  by apply submxMr; apply row_sub.
- by apply/eqP; by rewrite -{2}(mulmxK Uf (E^C)%MS) Hf4. 
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
 apply submx_full; apply sumsmx_compl_full.
case/sub_sumsmxP => x.
rewrite {-1}(_:delta_mx 0 i = (delta_mx 0 i - x) + x); 
 last by rewrite GRing.Theory.subrK.
do 2!move/submxP => [? ->].
by rewrite mulmx_addl -2!mulmxA Hf1 Hf2.
Qed.
