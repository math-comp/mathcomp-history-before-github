Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import ssralg bigops matrix.

Open Local Scope ring_scope.
Open Local Scope matrix_scope.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section GaussianElimination.
Variable F : fieldType.
Variables m n : nat.
Notation Local "''M_' ( m , n )" := (matrix F m n) : type_scope.
Implicit Type A B C : 'M_(m, n).

(* Row Operations *)
Definition mx_row_scale A i0 c :=
 \matrix_(i, j) if i == i0 then c * A i j else A i j.

Definition mx_row_exchange A i1 i2 :=
 \matrix_(i, j) if i == i1 then A i2 j else if i== i2 then A i1 j else A i j.

Definition mx_row_repl A i1 i2 c :=
 \matrix_(i, j) if i == i1 then A i j + c * A i2 j else A i j.

(* RREF operations *)
(* annihilate all element of a colum expect the pivot *)
Definition annihilate_col_fun i j x A :=
 if i != x then mx_row_repl A x i (-(A x j) * (A i j)^-1) else A.

Lemma annihilate_col_funE : forall A i j x k l,
  (annihilate_col_fun i j x A) k l =
  if (i != x) && (k == x) then A k l - (A k j) * (A i j)^-1 * A i l else A k l.
Proof.
move=> A i j x k l; case: ifP; rewrite /annihilate_col_fun.
  by case/andP=> ->; move/eqP<-; rewrite mxE eq_refl !mulNr.
by case/nandP; [move/negbTE-> | case: ifP => // _; rewrite mxE; move/negbTE->].
Qed.

Definition annihilate_col A i j :=
 foldr (annihilate_col_fun i j) A (take m (enum 'I_m)).

Lemma annihilate_colE : forall A i j k l,
 (annihilate_col A i j) k l =
 if (k != i) then A k l - (A k j) * (A i j)^-1 * A i l else A k l.
Proof.
move=> /= A i j k l; rewrite /annihilate_col.
elim: {1 4 10}m (leqnn m) (ltn_ord k) A => [// | m' Rm' Lm' Lk A].
rewrite (take_nth k) 1?size_enum_ord // -cats1 (nth_ord_enum _ (Ordinal Lm')).
rewrite foldr_cat /=; rewrite ltnS leq_eqVlt orbC in Lk; case/orP: Lk => Lk.
  rewrite (Rm' (ltnW Lm')) // !annihilate_col_funE.
  suff -> : k == Ordinal Lm' = false; first by rewrite andbF andNb.
  apply/eqP; move/(congr1 (@nat_of_ord _)); move/eqP.
  by rewrite /= eqn_leq andbC leqNgt Lk.
suff <- : k = (Ordinal Lm'); [| apply: val_inj]; rewrite /= -(eqP Lk) //{Rm' Lk}.
elim: {-2}(val k) {m' Lm'} (leqnn k) A => /= [| k' Rk'] Lk A.
  by rewrite take0 /= annihilate_col_funE eq_refl andbT eq_sym.
have Hk' : k' < m by apply (ltn_trans Lk).
rewrite (take_nth k) 1?size_enum_ord // -cats1 foldr_cat. 
rewrite (nth_ord_enum _ (Ordinal Hk')) /=.
have -> : annihilate_col_fun i j (Ordinal Hk') (annihilate_col_fun i j k A) = 
 annihilate_col_fun i j k (annihilate_col_fun i j (Ordinal Hk') A).
  apply/matrixP=> ? ?; rewrite !annihilate_col_funE !andNb.
  by case: ifP => -> //; case: ifP => ->.
rewrite (Rk' (ltnW Lk)) !annihilate_col_funE andNb //.
suff -> : k == (Ordinal Hk') = false; [by rewrite andbF | apply/eqP].
by move/(congr1 (@nat_of_ord _)) => /=; move/eqP; rewrite eqn_leq leqNgt Lk.
Qed.

Definition rref_pred (r : nat) A j := 
 let P := [pred k | forallb l : 'I_m, (r <= l < k) ==> (A l j == 0)] in
 [pred k | [&& (A k j != 0), (r <= k) & P k]].

Lemma rref_predP : forall r A j,
 reflect (forall x : 'I_m, r <= x -> A x j = 0) (pred0b (rref_pred r A j)).
Proof.
move=> /= r A j; apply: (iffP idP) => H; rewrite /rref_pred; last first.
  apply/pred0P => /= k /=; case: (leqP r k) => rk; rewrite /= 1?andbF //.
  by move: (H _ rk); move/eqP->.
move/negPn: H; rewrite negb_exists; move/forallP => H /= k.
elim: {1}(val k) {1 3 4}k (leqnn k) => [| k' Rk'] l Hl Lrl.
  move: (H l); move: (leq_trans Lrl Hl); move: Hl; rewrite !leqn0; move/eqP->.
  by move/eqP => -> /=; case/nandP; [move/negPn; move/eqP | case/pred0P => ?].
rewrite leq_eqVlt ltnS in Hl; case/orP: Hl; last by move=> ?; apply: Rk'.
move=> Hl; move: (H l); rewrite Lrl; case/nandP; first by move/negPn; move/eqP.
case/existsP => /= l'; rewrite negb_imply (eqP Hl) ltnS; case/andP.
by case/andP => ? ?; rewrite (Rk' l') 1?eq_refl.
Qed.

Definition rref_fun (x : nat * 'M_(m, n)) (j : 'I_n) : nat * 'M_(m, n) :=
 let s_i := pick (rref_pred x.1 x.2 j) in 
 if (insub x) : option {y | (x.1 < m) } is Some (exist _ Hx) then
  if s_i is Some i then
   let A1 := mx_row_exchange x.2 (Ordinal Hx) i in 
   let A2 := mx_row_scale A1 (Ordinal Hx) (A1 (Ordinal Hx) j)^-1 in 
   let A3 := annihilate_col A2 (Ordinal Hx) j in
    ((x.1).+1, A3)
  else x
 else x.

(* Compute the rref form of a given matrix and it's rank *)
Definition rref A j := foldl rref_fun (0%N, A) (take j (enum 'I_n)).

Definition rank A := (rref A n).1.
Definition rref_mx A := (rref A n).2.

(* Definition of rref predicate *)
Definition zrow A i j := (forallb k : 'I_n, (k < j) ==> (A i k == 0)).

Lemma zrowP : forall A i j,
 reflect (forall k : 'I_n, k < j -> (A i k = 0)) (zrow A i j).
Proof.
move=> /= A i j.
apply: (iffP idP) => H; last by apply/forallP=> ?; apply/implyP; move/H->.
by move=> /= k Hk; move/forallP: H; move/(_ k); rewrite Hk /=; move/eqP.
Qed.

(* getting the pivot *)
Definition pivot A i j :=
 pick [pred l | [&& (A i l != 0), (l < j) & (zrow A i l)]].

Definition zrows_in_bottom A j :=
 forallb i, (zrow A i j) ==> (forallb i' : 'I_m, ((i <= i') ==> zrow A i' j)).

Definition pivot_eq1 A j :=
 forallb i, if (pivot A i j) is Some l then A i l == 1 else zrow A i j.

Definition pivot_zcol A j := forallb i,
 if (pivot A i j) is Some l then (forallb k, (k != i) ==> (A k l == 0))
 else true.

Definition pivot_mono A j := forallb i1,
 if (pivot A i1 j) is Some j1 then
  forallb i2, if pivot A i2 j is Some j2 then (i1 < i2) ==> (j1 < j2) else true
 else true.

Definition is_rref A :=
 [&& zrows_in_bottom A n, pivot_eq1 A n, pivot_zcol A n & pivot_mono A n].

Section InvariantLemmas.

Lemma rank_rref_mono : forall A j j', j <= j' -> (rref A j).1 <= (rref A j').1.
Proof.
move=> A j; elim=> [| j' Rj']; first by rewrite leqn0; move/eqP->.
rewrite leq_eqVlt ltnS; case/orP => Ljj'; first by move/eqP: Ljj' ->.
rewrite (leq_trans (Rj' Ljj')) // /rref.
case: (leqP n j') => H; last rewrite (take_nth (Ordinal H)) 1?size_enum_ord //.
  by rewrite !take_oversize 1?size_enum_ord 1?(leq_trans H).
rewrite -cats1 foldl_cat /= (nth_ord_enum _ (Ordinal H)) {2}/rref_fun.
by case: insubP => //= [] [] _ ? _ _; case: pickP => [| ?] /=.
Qed.

Lemma rank_rref_leq : forall A j, (rref A j).1 <= minn m j.
Proof.
move=> A; elim=> [| j]; rewrite /rref 1?take0 //=.
case: (leqP n j) => Hj.
  rewrite !take_oversize 1?size_enum_ord 1?(leq_trans Hj) // !leq_minr. 
  by case/andP=> -> /= H; apply: (leq_trans H).
rewrite (take_nth (Ordinal Hj)) 1?size_enum_ord // -cats1 foldl_cat /=.
rewrite (nth_ord_enum _ (Ordinal Hj)) {2}/rref_fun /=.
case: insubP => //= [[] [] _ _ Hm _ _ /=| _]; last first.
  by rewrite !leq_minr; case/andP => -> /= H; apply: (leq_trans H).
case: pickP => [/= k | _]; last first.
  by rewrite !leq_minr; case/andP => -> /= H; apply: (leq_trans H).
by case/and3P=> H1 H2 _; rewrite !leq_minr ltnS Hm; case/andP=> _ ->.
Qed.

Lemma rref_mx_zcols : forall A (i : 'I_m) (j : 'I_n) j',
 j < j' -> (rref A j').1 <= i -> (rref A j').2 i j = 0.
Proof.
move=> A i j j'; elim: j' i j => // j' Rj' i j; rewrite ltnS leq_eqVlt => Ljj'.
case: (leqP n j') => Hj'; first move: (Rj' i j (leq_trans (ltn_ord j) Hj')).
  by rewrite /rref !take_oversize 1?size_enum_ord 1?(leq_trans Hj').
rewrite /rref (take_nth j) 1?size_enum_ord // -cats1 foldl_cat.
rewrite (nth_ord_enum _ (Ordinal Hj')) /= {1 3}/rref_fun /=.
case: insubP => // [[] [] _ _ H0 _ _ |]; last first. 
  by move=> H1 ?; move: H1; rewrite (leq_ltn_trans _ (ltn_ord i)).
case: pickP => /= [k |]; first case/and3P=> H1 H2 _; last first.
  case/orP: Ljj' => [| ? ? ?]; last by apply: Rj'.
  move/eqP=> jj'; move/pred0P; move/rref_predP=> H1 H2.
  by suff -> : j = Ordinal Hj'; [apply: H1 | apply: val_inj].
rewrite annihilate_colE !mxE eqxx mulVf // !invr1 !mulr1. 
case: ifP; [move/negbTE=> -> H3 | by move/eqP->; rewrite ltnn].
case/orP: Ljj' => Ljj'; first move/eqP: Ljj' => Ljj' ; last first.
  by rewrite !(Rj' _ j) 1?(ltnW H3) // !mulr0 oppr0 addr0 if_same.
by suff -> : j = (Ordinal Hj'); [ rewrite mulVf // mulr1 addrN | apply: val_inj].
Qed.

Lemma rref_mxE : forall A i j, (rref_mx A) i j = (rref A j.+1).2 i j.
Proof.
move=> /= A i j; rewrite /rref_mx.
elim: {1 5 8}n (leqnn n) j (ltn_ord j) => // n' Rn' Ln j; rewrite ltnS leq_eqVlt.
case/orP => [| Ljm']; last rewrite -Rn' // 1?ltnW //; first by move/eqP->.
rewrite /rref (take_nth j) 1?size_enum_ord // -cats1 foldl_cat.
rewrite (nth_ord_enum _ (Ordinal Ln)) /= {1}/rref_fun /=.
case: insubP=> //= [] [] _ H0 _ _; case: pickP => //= k; case/and3P=> H1 H2 H3.
rewrite !annihilate_colE !mxE /= eqxx (rref_mx_zcols Ljm') // !mulr0 oppr0 addr0.
case: ifP; last by move/eqP->; rewrite eqxx mulr0 rref_mx_zcols.
by move/negbTE->; case: ifP => //; move/eqP->; rewrite !rref_mx_zcols.
Qed.

Lemma zrow_rank_leq : forall A i j, zrow (rref_mx A) i j -> (rref A j).1 <= i.
Proof.
move=> /= A i; elim=> [| j]; rewrite /rref 1?take0 // => Rj Zj.
have : zrow (rref_mx A) i j.
  by apply/zrowP => k Hk; move/zrowP: Zj => -> //; apply: (ltn_trans Hk).
case : (leqP n j) => Hj; move/Rj.
  by rewrite !take_oversize 1?size_enum_ord // (leq_trans Hj).
move/zrowP: Zj; move/(_ (Ordinal Hj) (ltnSn j)); rewrite rref_mxE /rref.
rewrite (take_nth (Ordinal Hj)) 1?size_enum_ord // -cats1 foldl_cat.
rewrite (nth_ord_enum _ (Ordinal Hj)) /= {1 4}/rref_fun /=.
case: insubP => //= [] [] _ H0 _ _; case: pickP => //= l; case/and3P=> H1 H2 _.
rewrite ltn_neqAle andbC annihilate_colE !mxE eqxx mulVf // !invr1 !mulr1.
case: ifP; last by move/eqP->; move/eqP; rewrite !eqxx mulVf // oner_eq0.
by move/negbTE=> H _ -> /=; apply/eqP=> ?; case/eqP: H; apply: val_inj.
Qed.

End InvariantLemmas.

Lemma zrows_in_bottom_rref : forall A, zrows_in_bottom (rref_mx A) n.
Proof.
move=> A; apply/forallP => /= i; apply/implyP; move/zrowP => Zrn.
apply/forallP => /= i'; apply/implyP => l_ii'; apply/zrowP=> k _.
rewrite rref_mxE rref_mx_zcols 1?(leq_trans _ l_ii') //; apply: zrow_rank_leq.
by apply/zrowP => ? _; apply: Zrn.
Qed.

Lemma pivot_eq1_rref : forall A, pivot_eq1 (rref_mx A) n.
Proof.
move=> A; apply/forallP => /= i; rewrite /pivot.
case: pickP => /= [j | Pz]; last apply/zrowP => j _; last first.
  elim: {1}(val j) {1 3}j (leqnn j) => [| l Rl] {j}j Lj.
  - move: (Pz j); move: Lj; rewrite /= (ltn_ord j) leqn0 andbC; move/eqP->.
    by suff -> : zrow (rref_mx A) i 0 => /=; [move/eqP | apply/zrowP => ?].
  rewrite leq_eqVlt ltnS orbC in Lj; case/orP: Lj => Lj; first by apply: Rl.
  move: (Pz j); rewrite /= (ltn_ord j) andbC.
  suff -> : zrow (rref_mx A) i j => /=; first by move/eqP.
  by apply/zrowP=> ? ?; apply: Rl; rewrite -ltnS -(eqP Lj).
rewrite rref_mxE /rref; case/and3P => H1 _ Zj; move: H1.
rewrite (take_nth j) 1?size_enum_ord // (nth_ord_enum _ j) -cats1 foldl_cat /=.
rewrite {1 3}/rref_fun /=; case: insubP => /= [[] [] _ _ H0 _ _|]; last first.
  by rewrite (leq_ltn_trans _ (ltn_ord i)) => //; apply: zrow_rank_leq.
case: pickP => //= [k |]; last move/pred0P; last first.
  by move/rref_predP; move/(_ i)->; rewrite 1?eq_refl //; apply: zrow_rank_leq.
case/and3P => H1 H2 _; rewrite annihilate_colE !mxE eqxx mulVf // !invr1 !mulr1.
by case: ifP; [move/negbTE-> | move/eqP->]; rewrite 1?addrN eqxx 1?mulVf.
Qed.

Lemma pivot_zcol_rref : forall A, pivot_zcol (rref_mx A) n.
Proof.
move=> A; apply/forallP => /= i; rewrite /pivot.
case: pickP => //= j; case/and3P => Hj1 _ Hj2; apply/forallP=> /= k.
apply/implyP=> Hk; move: Hj1; rewrite !rref_mxE /rref.
rewrite (take_nth j) 1?size_enum_ord // -cats1 (nth_ord_enum _ j) foldl_cat /=.
rewrite {1 3}/rref_fun; case: insubP=> /= [[] [] _ _ H0 _ _ |]; last first.
  by rewrite (leq_ltn_trans _ (ltn_ord i)) //; apply: zrow_rank_leq.
case: pickP=> /= [l |]; last move/pred0P; last first.
  by move/rref_predP; move/(_ i)->; rewrite 1?eq_refl //; apply: zrow_rank_leq.
case/and3P=> H1 H2 H3; rewrite !annihilate_colE !mxE eqxx mulVf // !invr1 !mulr1.
by case: ifP; [move/negbTE-> | move/eqP<-]; rewrite 1?addrN eqxx 1?mulVf 1?Hk.
Qed.

Lemma pivot_mono_rref : forall A, pivot_mono (rref_mx A) n.
Proof.
move=> A; apply/forallP=> /= i; rewrite /pivot.
case: pickP=> //= j; case/and3P=> Hj1 _ Hj2; apply/forallP=> /= k.
case: pickP=> //= l; case/and3P=> Hl1 _ Hl2; apply/implyP=> ik.
case: (ltngtP j l)=> // lj.
  case/eqP: Hl1; suff : zrow (rref_mx A) k j; first by move/zrowP->.
  apply/zrowP=> y ?; rewrite rref_mxE rref_mx_zcols 1?(leq_trans _ (ltnW ik)) //.
  by apply: (leq_trans _ (zrow_rank_leq Hj2)); apply: rank_rref_mono.
suff : rref_mx A k l == 0; first by rewrite (negbTE Hl1).
suff <- : j = l :> 'I_n; first apply/eqP; last by apply: val_inj.
move: Hj1; rewrite !rref_mxE /rref (take_nth j) 1?size_enum_ord // -cats1.
rewrite (nth_ord_enum _ j) foldl_cat /= {1 3}/rref_fun /=.
case: insubP=> //= [[] [] _ _ H0 _ _ |]; last first.
  by rewrite (leq_ltn_trans _ (ltn_ord i)) //; apply: zrow_rank_leq.
case: pickP=> //= [l' |]; last move/pred0P; last first.
  by move/rref_predP; move/(_ i)->; rewrite 1?eq_refl //; apply: zrow_rank_leq.
case/and3P=> H1 H2 H3; rewrite !annihilate_colE !mxE eqxx mulVf // !invr1 !mulr1.
by case: ifP; [move/negbTE-> | move/eqP<-]; rewrite addrN eqxx neq_ltn orbC 1?ik.
Qed.

Lemma is_rref_rref : forall A, is_rref (rref_mx A).
Proof.
move=> A; rewrite /is_rref.
by rewrite zrows_in_bottom_rref pivot_eq1_rref pivot_zcol_rref pivot_mono_rref.
Qed.

Lemma rank_min : forall A, rank A <= minn m n.
Proof. by move=> A; apply: rank_rref_leq. Qed.

End GaussianElimination.

Section LinearSystem.

End LinearSystem.