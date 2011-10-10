(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg matrix zmodp div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section ExtraBigOp.

Lemma sumr_add : forall (R : ringType) m n (F : 'I_(m + n) -> R),
  \sum_(i < m + n) F i = \sum_(i < m) F (lshift _ i)
  + \sum_(i < n) F (rshift _ i).
Proof.
move=> R; elim=> [|m ihm] n F.
  rewrite !big_ord0 add0r; apply: congr_big=> // [[i hi]] _.
  by rewrite /rshift /=; congr F; apply: val_inj.
rewrite !big_ord_recl ihm -addrA.
congr (_ + _); first by congr F; apply: val_inj.
congr (_ + _); by apply: congr_big=> // i _ /=; congr F; apply: val_inj.
Qed.

(* Lemma lshift_l : forall m n (i : 'I_m), lshift n i  *)

Lemma allpairs_pair_map : forall S T S' T' (fx : S -> S') (fy : T -> T')
  (xs : seq S) (ys : seq T),
  [seq (x ,y) | x <- map fx xs, y <- map fy ys]
  = map (fun c => (fx c.1, fy c.2)) [seq (x, y) | x <- xs, y <- ys].
Proof.
move=> S T S' T' fx fy; elim=> [|x xs ihxs] ys //=.
by rewrite ihxs map_cat -!map_comp.
Qed.

Lemma map_pairl : forall (S T : eqType) (x0 : S) (ys : seq T),
  forall x y, ((x, y) \in (map (pair x0) ys)) = (x == x0) && (y \in ys).
Proof.
move=> S T x0; elim=> [|y0 ys ihys] x y /=.
  by rewrite !in_nil andbF.
by rewrite !in_cons ihys xpair_eqE -andb_orr.
Qed.

(* Lemma enum_val_mxvecSn : forall m n i, *)
(*   enum_val (cast_ord (esym (mxvec_cast (1 + m) n)) i) *)
(*   = match split (cast_ord (muln_addl _ _ _) i) with *)
(*       | inl p => (ord0, cast_ord (mul1n _) p) *)
(*       | inr p => let e := enum_val (cast_ord (esym (mxvec_cast m n)) p) *)
(*         in (lift ord0 e.1, e.2) *)
(*     end. *)
(* Proof. *)
(* move=> m n i. *)
(* case: splitP=> j /= hj. *)
(*   set r := (_ , _). *)
(*   rewrite (enum_val_nth r) /= enumT [Finite.enum _]unlock /=. *)
(*   rewrite /prod_enum /= enum_ordS /= nth_cat size_map size_enum_ord. *)
(*   have hjn: (j < n)%N by rewrite -{2}[n]mul1n. *)
(*   rewrite hj hjn /= (nth_map r.2) ?size_enum_ord //=. *)
(*   by congr (_, _); apply: val_inj=> /=; rewrite nth_enum_ord. *)
(* set e := (enum_val _) : {: 'I_m * 'I_n }. *)
(* rewrite /e (enum_val_nth (lift ord0 e.1, e.2)) (enum_val_nth e). *)
(* rewrite !enumT ![Finite.enum _]unlock /=. *)
(* rewrite /prod_enum /= enum_ordS /= nth_cat size_map size_enum_ord. *)
(* rewrite ltnNge hj {1}mul1n leq_addr /=. *)
(* rewrite allpairs_pair_map -enumT /= mul1n addKn. *)
(* by rewrite (nth_map e) // size_allpairs !size_enum_ord ltn_ord. *)
(* Qed. *)

Lemma enum_rank_lift1l : forall m n (i : 'I_m) (j : 'I_n),
  enum_rank (lift ord0 i, j) = (n + (enum_rank (i, j)))%N :> nat.
Proof.
move=> m n i j.
rewrite /enum_rank /enum_rank_in.
rewrite ![enum {: _ * _}]enumT.
rewrite ![Finite.enum]unlock /=.
rewrite /prod_enum ?enum_ordS /=.
rewrite allpairs_pair_map /= index_cat size_map size_enum_ord -enumT.
have hij: (lift ord0 i, j) = (fun c => (lift ord0 c.1, c.2)) (i, j) by [].
rewrite map_pairl !hij index_map //=; last first.
  by move=> [x1 x2] [y1 y2] /= []; move/val_inj=> -> ->.
rewrite !insubdK // !cardE ?[enum {: _ * _}]enumT
  ![Finite.enum]unlock /prod_enum /= [_ \in _]inE -[_ _]/(_ (_ < _)%N).
  by rewrite index_mem; apply/allpairsP; exists (i,j)=> /=; rewrite !mem_enum.
rewrite /prod_enum enum_ordS /= size_cat size_map size_enum_ord ltn_add2l.
set a1 := allpairs _ _ _; set a2 := allpairs _ _ _.
suff: size a2 = size a1.
  move->; rewrite index_mem.
  by apply/allpairsP; exists (i,j)=> /=; rewrite !mem_enum.
by rewrite /a1 /a2 !(size_allpairs, size_map).
Qed.

Lemma enum_rank_0l : forall m n (j : 'I_n),
  enum_rank (ord0 : 'I_m.+1, j) = j%N :> nat.
Proof.
move=> m n j.
rewrite /enum_rank /enum_rank_in.
rewrite ![enum {: _ * _}]enumT ![Finite.enum]unlock /=.
rewrite /prod_enum ?enum_ordS /=.
rewrite allpairs_pair_map /= index_cat size_map size_enum_ord -enumT.
rewrite map_pairl index_map //=; last by move=> x y [].
rewrite index_enum_ord mem_enum /=.
rewrite insubdK //= !cardE enumT [Finite.enum]unlock /= /prod_enum /=.
rewrite size_allpairs !size_enum_ord /mem /in_mem /=.
by rewrite (leq_trans (ltn_ord _)) // leq_pmull.
Qed.


Lemma enum_rank_nat : forall m n (i : 'I_m) (j : 'I_n),
  enum_rank (i, j) = (i * n + j)%N :> nat.
Proof.
elim=> [|m ihm] n i j; first by case: i.
case: i=> [[|i] hi].
  have ->: Ordinal hi = ord0 by apply: val_inj.
  by rewrite enum_rank_0l mul0n.
have hi': i < m by move: hi; rewrite ltnS.
have ->: Ordinal hi = lift ord0 (Ordinal hi') by apply: val_inj.
by rewrite enum_rank_lift1l ihm /= addnA -mulSn.
Qed.

Lemma enum_rank_nat_inj : forall m m' n n', n = n' ->
  forall (i : 'I_m) (j : 'I_n) (i' : 'I_m') (j' : 'I_n'),
  enum_rank (i, j) = enum_rank (i', j') :> nat
  -> (i :nat, j: nat) = (i' : nat, j' :nat).
Proof.
move=> m m' n n' en i j i' j' hij; apply/eqP=> /=.
move: hij; rewrite !enum_rank_nat /= -{1}en xpair_eqE=> hij.
move: (erefl ((i * n + j) %% n)%N).
rewrite {1}hij !modn_addl_mul !modn_small ?ltn_ord ?en // => hj.
move: hij; rewrite hj; move/addIn; move/eqP; rewrite eqn_mul2r.
case n0: (_ == _)=> //=; last by move/eqP->; rewrite !eqxx.
by case: j {hj}=> j hj; move: hj (hj); rewrite (eqP n0).
Qed.

Lemma mulr_sum : forall (R : ringType) m n (Fm : 'I_m -> R) (Fn : 'I_n -> R),
  (\sum_(i < m) Fm i) * (\sum_(i < n) Fn i)
  = \sum_(i < m * n) (
    (Fm (enum_val (cast_ord (esym (mxvec_cast _ _)) i)).1)
    * (Fn (enum_val (cast_ord (esym (mxvec_cast _ _)) i)).2)).
Proof.
move=> R'.
elim=> [|m ihm] n Fm Fn /=; first  by rewrite !big_ord0 mul0r.
rewrite big_ord_recl /= mulr_addl ihm.
rewrite -[(m.+1*n)%N]/(n + m*n)%N.
rewrite sumr_add /=; congr (_ + _).
  rewrite -mulr_sumr; apply: congr_big=> // i _.
  set e := enum_val _; suff: e = (ord0, i) by move->.
  apply: enum_rank_inj; apply: val_inj.
  by rewrite enum_valK /= enum_rank_nat mul0n.
apply: congr_big=> //= i _.
set j := enum_val _; set e := enum_val _.
suff: e = (lift ord0 j.1, j.2) by move ->.
apply: enum_rank_inj; apply: val_inj=> /=.
by rewrite enum_rank_lift1l -surjective_pairing !enum_valK /=.
Qed.

End ExtraBigOp.

Section ExtraMx.

Lemma castmx_mul : forall  (R : ringType)
  (m m' n p p': nat) (em : m=m') (ep : p = p')
  (M : 'M[R]_(m,n)) (N : 'M[R]_(n,p)),
  castmx (em, ep) (M *m N) = castmx (em, erefl _) M *m castmx (erefl _, ep) N.
Proof.
move=> R0 m m' n p p' em ep M N; apply/matrixP=> i j; rewrite !castmxE !mxE /=.
by apply: congr_big=> //= k _; rewrite !castmxE /= cast_ord_id.
Qed.

Lemma mulmx_cast : forall  (R : ringType)
  (m n n' p p' : nat) (en : n' = n) (ep : p' = p)  (M : 'M[R]_(m,n)) (N : 'M[R]_(n',p')),
  M *m (castmx (en, ep) N) = (castmx (erefl _, (esym en)) M) *m (castmx (erefl _, ep) N).
Proof.
move=> R0 m n n' p p' en ep M N; apply/matrixP=> i j; rewrite !mxE /=.
rewrite (reindex_onto (cast_ord en) (cast_ord (esym en)) _) /=; last first.
  by move=>*; rewrite cast_ordKV.
apply: congr_big=> //; first by move=> k; rewrite /= cast_ord_comp cast_ord_id eqxx.
by move=> k _; rewrite !castmxE /= !cast_ord_id cast_ordK esymK.
Qed.

Lemma castmx_row :
   forall (R : Type) (m m' n1 n2 n1' n2' : nat)
     (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
     (eq_m : m = m') (A1 : 'M[R]_(m, n1)) (A2 : 'M_(m, n2)),
   castmx (eq_m, eq_n12) (row_mx A1 A2) =
   row_mx (castmx (eq_m, eq_n1) A1) (castmx (eq_m, eq_n2) A2).
Proof.
move=> R' m m' n1 n2 n1' n2' eq_n1 eq_n2 eq_n12 eq_m A1 A2.
apply/matrixP=> i j; rewrite !castmxE !mxE /=.
case: splitP=> j1 /= hj1.
  case: splitP=> j2 /= hj2; rewrite !castmxE /=; last first.
    by move: (ltn_ord j1); rewrite -hj1 hj2 ltnNge -eq_n1 leq_addr.
  by congr (A1 _ _); apply: val_inj=> /=; rewrite -hj1 -hj2.
case: splitP=> j2 /= hj2; rewrite !castmxE /=.
  by move: (ltn_ord j2); rewrite -hj2 hj1 ltnNge {1}eq_n1 leq_addr.
by congr (A2 _ _); apply: val_inj=> /=; move: hj1 hj2->; rewrite {1}eq_n1; move/addnI.
Qed.

Lemma castmx_col :
   forall (R : Type) (m m' n1 n2 n1' n2' : nat)
     (eq_n1 : n1 = n1') (eq_n2 : n2 = n2') (eq_n12 : (n1 + n2 = n1' + n2')%N)
     (eq_m : m = m') (A1 : 'M[R]_(n1, m)) (A2 : 'M_(n2, m)),
   castmx (eq_n12, eq_m) (col_mx A1 A2) =
   col_mx (castmx (eq_n1, eq_m) A1) (castmx (eq_n2, eq_m) A2).
Proof.
move=> R' m m' n1 n2 n1' n2' eq_n1 eq_n2 eq_n12 eq_m A1 A2.
rewrite -[castmx _ _]trmxK trmx_cast tr_col_mx /=.
by rewrite (castmx_row eq_n1 eq_n2) tr_row_mx !trmx_cast !trmxK.
Qed.

Lemma castmx_block :
   forall (R : Type) (m1 m1' m2 m2' n1 n2 n1' n2' : nat)
     (eq_m1 : m1 = m1') (eq_n1 : n1 = n1') (eq_m2 : m2 = m2') (eq_n2 : n2 = n2')
     (eq_m12 : (m1 + m2 = m1' + m2')%N) (eq_n12 : (n1 + n2 = n1' + n2')%N)
     (ul : 'M[R]_(m1, n1)) (ur : 'M[R]_(m1, n2)) (dl : 'M[R]_(m2, n1)) (dr : 'M[R]_(m2, n2)),
   castmx (eq_m12, eq_n12) (block_mx ul ur dl dr) =
   block_mx (castmx (eq_m1, eq_n1) ul) (castmx (eq_m1, eq_n2) ur)
   (castmx (eq_m2, eq_n1) dl) (castmx (eq_m2, eq_n2) dr).
Proof.
move=> R' m1 m1' m2 m2' n1 n2 n1' n2'.
move=> eq_n1 eq_m1 eq_n2 eq_m2 eq_n12 eq_m12 ul ur dl dr.
by rewrite !block_mxEv (castmx_col eq_n1 eq_n2) !(castmx_row eq_m1 eq_m2).
Qed.

End ExtraMx.

Section MxTens.

Variable R : ringType.

Definition tensmx {m n p q : nat}
  (A : 'M_(m, n)) (B : 'M_(p, q)) : 'M[R]_(_,_) := nosimpl
  castmx (mxvec_cast _ _, mxvec_cast _ _)
  (\matrix_(i, j) (A (enum_val i).1 (enum_val j).1 * B (enum_val i).2 (enum_val j).2)).

Notation "A *t B" := (tensmx A B)
  (at level 40, left associativity, format "A  *t  B").

Lemma tensmxE : forall {m n p q} (A : 'M_(m, n)) (B : 'M_(p, q)) i j k l,
  (A *t B) (mxvec_index i j) (mxvec_index k l) = A i k * B j l.
Proof. by move=> *; rewrite !castmxE !mxE !cast_ordK !enum_rankK. Qed.

Lemma tens0mx : forall {m n p q} (M : 'M[R]_(p,q)), (0 : 'M_(m,n)) *t M = 0.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(castmxE, mxE) mul0r. Qed.

Lemma tensmx0 : forall {m n p q} (M : 'M[R]_(m,n)), M *t (0 : 'M_(p,q)) = 0.
Proof. by move=> *; apply/matrixP=> i j; rewrite !(castmxE, mxE) mulr0. Qed.

Lemma tens_scalar_mx : forall
  (m n : nat) (c : R) (M : 'M_(m,n)),
  c%:M *t M = castmx (esym (mul1n _), esym (mul1n _)) (c *: M).
Proof.
move=> m n c M; apply/matrixP=> i j.
case: (mxvec_indexP i)=> i0 i1; case: (mxvec_indexP j)=> j0 j1.
rewrite tensmxE [i0]ord1 [j0]ord1 !castmxE !mxE /= mulr1n.
by congr (_ * M _ _); apply: val_inj=> /=; rewrite enum_rank_nat mul0n.
Qed.

Lemma tens_scalar1mx : forall (m n : nat) (M : 'M_(m,n)),
  1 *t M = castmx (esym (mul1n _), esym (mul1n _)) M.
Proof. by move=> m n M; rewrite tens_scalar_mx scale1r. Qed.

Lemma tens_scalarN1mx : forall (m n : nat) (M : 'M_(m,n)),
  (-1) *t M = castmx (esym (mul1n _), esym (mul1n _)) (-M).
Proof.
move=> m n M; rewrite [-1]mx11_scalar /= tens_scalar_mx !mxE.
by rewrite scaleNr scale1r.
Qed.

Lemma trmx_tens : forall {m n p q}
  (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)), (M *t N)^T = M^T *t N^T.
Proof.
by move=> m n p q M N; apply/matrixP=> i j; rewrite !(mxE, castmxE).
Qed.

Lemma tens_col_mx : forall {m n p q} (r : 'rV[R]_n)
  (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)),
  (col_mx r M) *t N =
  castmx (esym (muln_addl _ _ _), erefl _) (col_mx (r *t N) (M *t N)).
Proof.
move=> m n p q r M N; apply/matrixP=> i j.
case: (mxvec_indexP i)=> i0 i1; case: (mxvec_indexP j)=> j0 j1.
rewrite !tensmxE castmxE /= cast_ord_id esymK !mxE /=.
case: splitP=> i0' /= hi0'.
  case: splitP=> k /= hk.
    case: (mxvec_indexP k) hk=> k0 k1 /=; rewrite tensmxE.
    move/(enum_rank_nat_inj (erefl _))=> [] h0 h1.
    by congr (r _ _ * N _ _); apply:val_inj; rewrite /= -?h0 ?h1.
  move: hk (ltn_ord i1); rewrite enum_rank_nat hi0'.
  by rewrite [i0']ord1 mul0n mul1n add0n ltnNge=> ->; rewrite leq_addr.
case: splitP=> k /= hk.
  move: (ltn_ord k); rewrite -hk enum_rank_nat hi0' ltnNge {1}mul1n.
  by rewrite muln_addl {1}mul1n -addnA leq_addr.
case: (mxvec_indexP k) hk=> k0 k1 /=; rewrite tensmxE.
rewrite enum_rank_nat hi0' muln_addl -addnA -enum_rank_nat.
move/addnI; move/(enum_rank_nat_inj (erefl _))=> [h0 h1].
by congr (M _ _ * N _ _); apply:val_inj; rewrite /= -?h0 ?h1.
Qed.

Lemma tens_row_mx : forall {m n p q} (r : 'cV[R]_m)
  (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)),
  (row_mx r M) *t N =
  castmx (erefl _, esym (muln_addl _ _ _)) (row_mx (r *t N) (M *t N)).
Proof.
move=> m n p q r M N.
rewrite -[_ *t _]trmxK trmx_tens tr_row_mx tens_col_mx.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
by rewrite trmx_cast castmx_comp castmx_id tr_col_mx -!trmx_tens !trmxK.
Qed.

Lemma tens_block_mx : forall {m n p q}
  (ul : 'M[R]_1) (ur : 'rV[R]_n) (dl : 'cV[R]_m)
  (M :'M[R]_(m,n)) (N : 'M[R]_(p,q)),
  (block_mx ul ur dl M) *t N =
  castmx (esym (muln_addl _ _ _), esym (muln_addl _ _ _))
  (block_mx (ul *t N) (ur *t N) (dl *t N) (M *t N)).
Proof.
move=> m n p q ul ur dl M N.
rewrite !block_mxEv tens_col_mx !tens_row_mx -!cast_col_mx castmx_comp.
by congr (castmx (_,_)); apply nat_irrelevance.
Qed.


Fixpoint ntensmx_rec {m n} (A : 'M_(m,n)) k : 'M_(m ^ k.+1,n ^ k.+1) :=
  if k is k'.+1 then (A *t (ntensmx_rec A k')) else A.

Definition ntensmx {m n} (A : 'M_(m, n)) k := nosimpl
  match k return 'M[R]_(m ^ k,n ^ k) with
    | k'.+1 => ntensmx_rec A k'
    | 0 => 1
  end.

Notation "A ^t k" := (ntensmx A k)
  (at level 39, left associativity, format "A  ^t  k").


Lemma ntensmx0 : forall {m n} (A : 'M_(m,n)) , A ^t 0 = 1.
Proof. by []. Qed.

Lemma ntensmx1 : forall {m n} (A : 'M_(m,n)) , A ^t 1 = A.
Proof. by []. Qed.

Lemma ntensmx2 : forall {m n} (A : 'M_(m,n)) , A ^t 2 = A *t A.
Proof. by []. Qed.

Lemma ntensmxSS : forall {m n} (A : 'M_(m,n)) k, A ^t k.+2 = A *t A ^t k.+1.
Proof. by []. Qed.

Definition ntensmxS := (@ntensmx1, @ntensmx2, @ntensmxSS).

End MxTens.

Notation "A *t B" := (tensmx A B)
  (at level 40, left associativity, format "A  *t  B").

Notation "A ^t k" := (ntensmx A k)
  (at level 39, left associativity, format "A  ^t  k").

Section MapMx.
Variables (aR rR : ringType).
Hypothesis f : {rmorphism aR -> rR}.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Variables m n p q: nat.
Implicit Type A : 'M[aR]_(m, n).
Implicit Type B : 'M[aR]_(p, q).

Lemma map_mxT : forall A B, (A *t B)^f = A^f *t B^f :> 'M_(m*p, n*q).
Proof.
by move=> A B; apply/matrixP=> i j; rewrite !(castmxE, mxE) /= rmorphM.
Qed.

End MapMx.

Section Misc.

Lemma tensmx_mul : forall (R : comRingType) m n p q r s
  (A : 'M[R]_(m,n)) (B : 'M[R]_(p,q)) (C : 'M[R]_(n, r)) (D : 'M[R]_(q, s)),
  (A *t B) *m (C *t D) = (A *m C) *t (B *m D).
Proof.
move=> Ring m n p q r s A B C D.
apply/matrixP=> /= i j.
case (mxvec_indexP i)=> [im ip] {i}.
case (mxvec_indexP j)=> [jr js] {j}.
rewrite /tensmx !castmxE !mxE !cast_ordK !enum_rankK /= mulr_sum.
apply: congr_big=> // k _.
rewrite !castmxE !mxE !cast_ordK !enum_rankK /=.
by rewrite mulrCA !mulrA [C _ _ * A _ _]mulrC.
Qed.

Lemma tensmx_unit : forall (R : fieldType) m n (A : 'M[R]_m%N) (B : 'M[R]_n%N),
  m != 0%N -> n != 0%N ->
  A \in unitmx -> B \in unitmx -> (A *t B) \in unitmx.
Proof.
move=> Ring [|m] [|n] A B _ _ uA uB //.
suff : (A^-1 *t B^-1) *m (A *t B) = 1.
  by case/mulmx1_unit=> _.
rewrite tensmx_mul !mulVmx//.
apply/matrixP=> /= i j; rewrite !castmxE !mxE /=.
case hij : (i == j); first by rewrite (eqP hij) !eqxx mul1r.
case fij: (_ == _); last by rewrite mul0r.
case sij: (_ == _)=> //=; rewrite mul1r//; apply/eqP; rewrite oner_eq0.
rewrite -hij; move: (eqP fij) (eqP sij)=> [qij] [rij].
apply/eqP; apply: val_inj=> /=.
move: (mxvec_indexP i) (mxvec_indexP j) qij rij=> [i1 i2] [j1 j2].
by rewrite !cast_ordK !enum_rankK /= => -> ->.
Qed.


Lemma tens_mx_scalar : forall (R : comRingType)
  (m n : nat) (c : R) (M : 'M[R]_(m,n)),
  M *t c%:M = castmx (esym (muln1 _), esym (muln1 _)) (c *: M).
Proof.
move=> R0 m n c M; apply/matrixP=> i j.
case: (mxvec_indexP i)=> i0 i1; case: (mxvec_indexP j)=> j0 j1.
rewrite tensmxE [i1]ord1 [j1]ord1 !castmxE !mxE /= mulr1n mulrC.
by congr (_ * M _ _); apply: val_inj=> /=; rewrite enum_rank_nat muln1 addn0.
Qed.

Lemma tensmx_decr : forall (R : comRingType) m n (M :'M[R]_m) (N : 'M[R]_n),
  M *t N = (M *t 1%:M) *m (1%:M *t N).
Proof. by move=> R0 m n M N; rewrite tensmx_mul mul1mx mulmx1. Qed.

Lemma tensmx_decl : forall (R : comRingType) m n (M :'M[R]_m) (N : 'M[R]_n),
  M *t N = (1%:M *t N) *m (M *t 1%:M).
Proof. by move=> R0 m n M N; rewrite tensmx_mul mul1mx mulmx1. Qed.

End Misc.