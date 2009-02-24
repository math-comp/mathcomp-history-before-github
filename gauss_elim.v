Add LoadPath "../".
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

(* Row Operations *)
Definition mx_row_scale (A : 'M_(m, n)) i0 c :=
 \matrix_(i, j) if i == i0 then c * A i j else A i j.

Definition mx_row_exchange (A : 'M_(m, n)) i1 i2 :=
 \matrix_(i, j) if i == i1 then A i2 j else if i== i2 then A i1 j else A i j.

Definition mx_row_repl (A : 'M_(m, n)) i1 i2 c :=
 \matrix_(i, j) if i == i1 then A i j + c * A i2 j else A i j.

(* putting in reduced row echelon form *)

Definition annihilate_col_fun (i : 'I_m) (j : 'I_n) (k : 'I_m) (A : 'M_(m, n)) :=
 if i != k then mx_row_repl A k i (-(A k j) * (A i j)^-1) else A.

Lemma annihilate_col_funE : forall (i : 'I_m) (j : 'I_n) m' A k l,
  (annihilate_col_fun i j m' A) k l =
  if (i != m') && (k == m') then A k l - (A k j) * (A i j)^-1 * A i l else A k l.
Proof.
move=> i j m' A k l; symmetry; rewrite /annihilate_col_fun.
case: ifP; first case/andP.
  by move=> H1 H2; rewrite H1 /mx_row_repl mxE H2 -(eqP H2) !mulNr.
case/nandP; first by move/negbTE->.
by case: ifP => // _; rewrite /mx_row_repl mxE; move/negbTE->.
Qed.

Definition annihilate_col_step (i : 'I_m) (j : 'I_n) (A : 'M_(m, n)) m' :=
 foldr (annihilate_col_fun i j) A (take m' (enum 'I_m)).

Definition annihilate_col (i : 'I_m) (j : 'I_n) (A : 'M_(m, n)) :=
 annihilate_col_step i j A m.

Lemma annihilate_col_stepE : forall (i : 'I_m) (j : 'I_n) A m' k l,
 annihilate_col_step i j A m' k l =
 if (k != i) && (k < m') then A k l - (A k j) * (A i j)^-1 * A i l else A k l.
Proof.
move=> i j A m'; rewrite /annihilate_col_step.
elim: m' A => [| m' Hm'] A k l //=; first by rewrite take0 /= ltn0 andbF.
case: (ltnP m' m) => m'm.
  rewrite (take_nth (Ordinal m'm)) 1?size_enum_ord //.
  rewrite -(cats0 ( _ _)) cat_rcons (nth_ord_enum _ (Ordinal m'm)).
  rewrite foldr_cat Hm' /=.
  case: ifP; first (case/andP => ki km').
  - rewrite ki (ltn_trans km' (ltnSn _)) !annihilate_col_funE.
    suff : k != Ordinal m'm; last by rewrite neq_ltn km'.
    by move/negbTE=> ->; rewrite andbF andNb.
  case/nandP; last rewrite ltnNge; move/negPn; [move/eqP-> | move=> m'k].
  - by rewrite eq_refl /= annihilate_col_funE andNb.
  case: ifP; rewrite annihilate_col_funE; last case: ifP => //.
  - case/andP => ki km'; suff -> : Ordinal m'm = k.
    - by rewrite eq_sym eq_refl ki.
    by apply: val_inj => /=; apply/eqP; rewrite eqn_leq m'k -ltnS.
  by case/andP => im'; move/eqP=> -> /=; rewrite eq_sym im' ltnSn.
have -> : take m'.+1 (enum 'I_m) = take m' (enum 'I_m).
  by rewrite !take_oversize 1?size_enum_ord // (leq_trans m'm _).
rewrite Hm'; suff : (k < m') && (k < m'.+1).
  by case/andP=> -> ->; rewrite andbT.
by apply/andP; split; apply: (leq_trans (ltn_ord k) _); apply: (leq_trans m'm).
Qed.

Lemma annihilate_colE : forall i j A k l,
 annihilate_col i j A k l =
 if (k != i) then A k l - (A k j) * (A i j)^-1 * A i l else A k l.
Proof.
by move=> i j A k l; rewrite annihilate_col_stepE (ltn_ord k) andbT.
Qed.

Definition rref_fun (x : nat * 'M_(m, n)) (j : 'I_n) : nat * 'M_(m, n) :=
let s_i := pick [pred k | (x.2 k j != 0) && (x.1 <= k)] in 
if (insub x) : option {y | (x.1 < m) } is Some (exist _ Hx) then
 if s_i is Some i then
  let A1 := mx_row_exchange x.2 (Ordinal Hx) i in 
  let A2 := mx_row_scale A1 (Ordinal Hx) (A1 (Ordinal Hx) j)^-1 in 
  let A3 := annihilate_col (Ordinal Hx) j A2 in
   ((x.1).+1, A3)
 else x
else x.

Definition rref_step (A : 'M_(m, n)) j :=
 foldl rref_fun (0%N, A) (take j (enum 'I_n)).

(* Compute the rref form of a given matrix and it's rank *)
Definition rref (A : 'M_(m, n)) := rref_step (A : 'M_(m, n)) n.

Definition rank A := (rref A).1.
Definition rref_mx A := (rref A).2.

(* Definition of rref predicate *)
Definition pivot_nz (A : 'M_(m, n)) i j := pick [pred l | (A i l != 0) && (l < j)].

Definition z_row (A : 'M_(m, n)) i j := (forallb k : 'I_n, (k < j) ==> (A i k == 0)).

Definition all_zero_row_in_bottom (A : 'M_(m, n)) j :=
 forallb i, (z_row A i j) ==> (forallb i' : 'I_m, ((i <= i') ==> z_row A i' j)).

Definition pivot_nz_eq1 A j :=
 forallb i, if (pivot_nz A i j) is Some l then A i l == 1 else z_row A i j.

Definition pivot_nz_zcol A j := forallb i,
 if (pivot_nz A i j) is Some l then (forallb k, (k != i) ==> (A k l == 0))
 else true.

Definition pivot_mono A j := forallb i1,
 if (pivot_nz A i1 j) is Some j1 then
  (forallb i2,
   if (pivot_nz A i2 j) is Some j2 then (i1 < i2) ==> (j1 < j2)
   else true)
 else true.

Definition is_rref A :=
 [&& all_zero_row_in_bottom A n, pivot_nz_eq1 A n, pivot_nz_zcol A n & pivot_mono A n].

Section InvariantsLemmas.

Lemma rref_step_rank_mono : forall A j j',
 j <= j' -> (rref_step A j).1 <= (rref_step A j').1.
Proof.
move=> A j; elim=> [|j' Rj' ]; first by rewrite leqn0; move/eqP->.
rewrite leq_eqVlt ltnS; case/orP; first by move/eqP->.
move=> j'j; apply: (leq_trans (Rj' j'j) _); rewrite {2}/rref_step.
case: (leqP n j') => n_j'.
  by rewrite /rref_step !take_oversize 1?size_enum_ord // (leq_trans n_j').
rewrite (take_nth (Ordinal n_j')) 1?size_enum_ord // -cats1 foldl_cat /=.
rewrite -/(rref_step A j') (nth_ord_enum _ (Ordinal n_j')) /rref_fun.
by case: insubP => //= [] [] _ ? _ _; case: pickP => [|k] /=.
Qed.

Lemma rref_step_rank_leS : forall A j, (rref_step A j.+1).1 <= (rref_step A j).1.+1.
Proof.
move=> A j; case: (leqP n j) => n_j.
  by rewrite /rref_step !take_oversize 1?size_enum_ord // (leq_trans n_j).
rewrite {1}/rref_step.
rewrite (take_nth (Ordinal n_j)) 1?size_enum_ord // -cats1 foldl_cat /=.
rewrite -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /rref_fun.
by case: insubP => //= [] [] _ ? _ _; case: pickP => [|k] /=.
Qed.

Lemma rank_le_row : forall A j, (rref_step A j).1 <= m.
Proof.
move=> A; elim=> [|j Rj]; first by rewrite /rref_step take0.
case: (leqP n j) => n_j; first move: Rj.
  by rewrite /rref_step !take_oversize 1?size_enum_ord // 1?(leq_trans n_j).
rewrite /rref_step (take_nth (Ordinal n_j)) 1?size_enum_ord // -cats1.
rewrite foldl_cat /= -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /rref_fun.
by case: insubP => //= [] [] _ ? _ _; case: pickP => [|k] /=.
Qed.

Lemma rank_le_col : forall A j, (rref_step A j).1 <= j.
Proof.
move=> A; elim=> [|j Rj]; first by rewrite /rref_step take0 .
case: (leqP n j) => n_j; first move: Rj.
  rewrite /rref_step !take_oversize 1?size_enum_ord // 1?(leq_trans n_j) //.
  by move=> H; rewrite (leq_trans H _).
rewrite /rref_step (take_nth (Ordinal n_j)) 1?size_enum_ord // -cats1.
rewrite foldl_cat /= -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /rref_fun.
by case: insubP => //= [[] [] * /=|*]; first case: pickP => [*|*] /=; apply: (leq_trans Rj _).
Qed.

Lemma rref_fun_col_null : forall A (j : 'I_n) x (i : 'I_m),
 x < i -> (rref_fun (x, A) j).2 i j = 0.
Proof.
move=> A j x i x_i; rewrite /rref_fun.
case: insubP=> //=; last by rewrite (ltn_trans x_i _).
move=> [] /= _ x_m _ _; case: pickP => //= [k|]; last first.
  by move/(_ i)=> /=; rewrite (ltnW x_i) andbT; move/negPn; move/eqP.
case/andP=> Akj x_k; rewrite !annihilate_colE !mxE /=.
have i_ne_x : i != Ordinal x_m.
  apply/eqP; move/(congr1 (@nat_of_ord m)) => /=; move/eqP.
  by rewrite eq_sym eqn_leq [_ <= x]leqNgt x_i /= andbF.
by rewrite i_ne_x (negbTE i_ne_x) eqxx mulVf // invr1 !mulr1 addrN.
Qed.

Lemma rref_step_eq_rank : forall A (j : 'I_n),
 (rref_step A j).1 = (rref_step A j.+1).1 ->
 forall i : 'I_m, (rref_step A j).1 <= i -> (rref_step A j).2 i j = 0.
Proof.
move=> A j H1 i x_i; move: H1.
rewrite {2}/rref_step (take_nth j) 1?size_enum_ord // -cats1 foldl_cat /=.
rewrite -/(rref_step A j) (nth_ord_enum _ j) /rref_fun.
case: insubP => //= [ [] [] /= _ _ x_m _ _ |]; last first.
  by move: (leq_ltn_trans x_i (ltn_ord i)) => ->.
case: pickP; last by move/(_ i) => /=; rewrite x_i andbT; move/negPn; move/eqP.
move=> k //= _; case: {x_i x_m}(rref_step A j).1 => //= l; move/eqP.
by rewrite eq_sym eqn_leq ltnn.
Qed.

Lemma rref_step_nil_mx : forall A (i : 'I_m) (j : 'I_n) j',
 j < j' -> (rref_step A j').1 <= i -> (rref_step A j').2 i j = 0.
Proof.
move=> A i j j'; elim: j' i => // j' Rj' i H1 H2; case: (leqP n j') => n_j'.
  rewrite /rref_step !take_oversize 1?size_enum_ord // ?(leq_trans n_j') //.
  move: Rj'; rewrite {2}/rref_step.
  rewrite !take_oversize 1?size_enum_ord // ?(leq_trans n_j') // => -> //.
  - by rewrite (leq_trans _ n_j').
  rewrite (leq_trans _ H2) //; exact: rref_step_rank_mono.
rewrite /rref_step (take_nth j) 1?size_enum_ord // -cats1 foldl_cat /=.
rewrite -/(rref_step A j') (nth_ord_enum _ (Ordinal n_j')) /rref_fun.
have x_i : (rref_step A j').1 <= i.
  by rewrite (leq_trans _ H2) //; apply: rref_step_rank_mono.
case: insubP=> //= [ [] [] /= _ _ x_m _ _ |]; last first.
  by rewrite (leq_trans _ (ltn_ord i)).
case: pickP => //= [k|]; last first.
  move/(_ i)=> /=; rewrite x_i /= andbT; rewrite ltnS leq_eqVlt in H1.
  case/orP: H1 => H1; last by rewrite Rj'.
  suff -> : Ordinal n_j' = j; first by move/negPn; move/eqP.
  by apply: val_inj => /=; rewrite (eqP H1).
case/andP=> Akj x_k; rewrite !annihilate_colE !mxE /=.
case: ifP => H3; last first.
  move/negPn: H3 => H3; rewrite H3 eq_refl; rewrite ltnS leq_eqVlt in H1.
  case/orP: H1 => H1; last by rewrite Rj' ?mulr0.
  suff : (rref_step A (Ordinal n_j')).1 = (rref_step A (Ordinal n_j').+1).1.
  - by move/rref_step_eq_rank; move/(_ k x_k)=> /= H'; rewrite H' eqxx in Akj.
  by apply/eqP; rewrite /= eqn_leq rref_step_rank_mono //= (leq_trans H2 _) 1?(eqP H3).
rewrite (negbTE H3) eqxx /= mulVf // invr1 mulr1.
rewrite ltnS leq_eqVlt in H1; move: Akj.
case/orP: H1 => H1; last by rewrite !Rj' //= if_same !mulr0 oppr0 addr0.
suff -> : Ordinal n_j' = j; last by apply: val_inj => /=; rewrite (eqP H1).
by move/mulVf->; rewrite mulr1; case: ifP; rewrite addrN.
Qed.

(* Proving that the value of a col j is given by the step j.+1 *)
Lemma rref_step_col : forall A (j : 'I_n) j', j < j' ->
 (forall i, (rref_step A j').2 i j = (rref_step A j.+1).2 i j).
Proof.
move=> A j; elim=> // j' Hj'; rewrite ltnS leq_eqVlt.
case/orP => [|j_j' i]; first by move/eqP->.
rewrite -Hj' //; case: (leqP n j') => nj'.
  by rewrite /rref_step !take_oversize 1?size_enum_ord // (leq_trans nj' _).
rewrite {1}/rref_step (take_nth j) 1?size_enum_ord // -cats1 foldl_cat /=.
rewrite (nth_ord_enum _ (Ordinal nj')) {Hj'}/= -/(rref_step A j').
elim: j' {-2}j' (leqnn j') j j_j' nj' A => [| k Hk] j' Hj' j j_j' nj' A.
  by rewrite leqn0 in Hj'; rewrite (eqP Hj') in j_j'.
rewrite leq_eqVlt in Hj'; case/orP: Hj' => Hj'; last by rewrite (Hk j' _ _ _ nj').
move: nj'; rewrite (eqP Hj') /rref_fun => nk.
case: insubP=> //= [] [] _ x_m _ _; case: pickP => //= l; case/andP=> H1 H2.
rewrite !annihilate_colE !mxE /= eqxx /=.
case: ifP => H3; last move/negPn: H3 => H3; rewrite ?H3 ?(negbTE H3).
  case: ifP => H4; rewrite H4.
  - rewrite mulVf // invr1 !mulr1 (eqP H4).
    have H5 : (rref_step A k.+1).2 l j = 0.
      by rewrite rref_step_nil_mx // -(eqP Hj').
    by rewrite H5 !mulr0 oppr0 addr0 rref_step_nil_mx // -(eqP Hj').
  rewrite mulVf // invr1 !mulr1 (@rref_step_nil_mx _ l j) // -1?(eqP Hj') //.
  by rewrite !mulr0 oppr0 addr0.
symmetry; rewrite rref_step_nil_mx //; last (by rewrite (eqP H3)); last by rewrite -(eqP Hj').
by rewrite (@rref_step_nil_mx _ l j) // 1?mulr0 // -(eqP Hj').
Qed.

Lemma rref_mx_colE : forall A i j, (rref_mx A) i j = (rref_step A j.+1).2 i j.
Proof. by move=> A i j; rewrite /rref_mx (rref_step_col _ (ltn_ord j)). Qed.

Lemma zrow_in_bottom : forall (A : matrix F m n) i j,
 z_row (rref_step A j).2 i j -> (rref_step A j).1 <= i.
Proof.
move=>A /= i; elim=> [_| j Rj Zri]; first by rewrite /rref_step take0.
case: (leqP n j) => n_j; first move: Rj Zri.
  rewrite /rref_step !take_oversize 1?size_enum_ord // ?(leq_trans n_j) //.
  move=> H1 H2; apply: H1; apply/forallP => /= k; apply/implyP => k_j.
  by move/forallP: H2; move/(_ k); move/implyP->; rewrite // (ltn_trans k_j).
have x_i : (rref_step A j).1 <= i.
  apply: Rj; apply/forallP => /= k; apply/implyP => k_j.
  move/forallP: Zri; move/(_ k); move/implyP.
  by rewrite rref_step_col 1?(ltn_trans k_j) // (rref_step_col _ k_j) => ->.
case: (leqP (rref_step A j.+1).1 (rref_step A j).1) => H1.
  suff -> : (rref_step A j.+1).1 = (rref_step A j).1; first done.
  by apply/eqP; rewrite eqn_leq H1 rref_step_rank_mono.
move: (rref_step_rank_leS A j) => H2.
have {H1 H2}Sx : (rref_step A j.+1).1 = (rref_step A j).1.+1.
  by apply/eqP; rewrite eqn_leq H1 H2.
rewrite Sx ltn_neqAle; apply/andP; split => //; apply/eqP => {x_i}x_i.
move/forallP: Zri => Zri; move: (Zri (Ordinal n_j)); move/implyP; move/(_ (ltnSn _)).
move/eqP; move: Sx; rewrite x_i /rref_step.
rewrite (take_nth (Ordinal n_j)) 1?size_enum_ord // -cats1 foldl_cat.
rewrite -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /= /rref_fun.
case: insubP => //= [[] [] /= _ _ x_m _ _|]; last by rewrite x_i ltn_ord.
case: pickP => //= [k |_]; last first.
  by rewrite x_i; move/eqP; rewrite eq_sym eqn_leq ltnn /=.
case/andP=> Akj x_k _; rewrite annihilate_colE !mxE eq_refl /=.
suff -> : (i == k) = false.
  suff -> : i == Ordinal x_m => /=; first rewrite mulVf //.
    by move/eqP; rewrite oner_eq0.
  by apply/eqP; apply: val_inj => /=; rewrite x_i.
case: (_ =P _) => // ik; rewrite -ik in Akj.
move: (Zri (Ordinal n_j)); move/implyP; move/(_ (ltnSn _)).
rewrite /rref_step (take_nth (Ordinal n_j)) 1?size_enum_ord // -cats1 foldl_cat.
rewrite -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /= /rref_fun.
case: insubP => //= [[] [] /= _ _ x'_m _ _|]; last by rewrite x_i ltn_ord.
case: pickP => //= [k' |_]; last by move/eqP=> H'; rewrite H' eqxx in Akj.
case/andP=> Ak'j x'_k'; rewrite annihilate_colE !mxE eq_refl /=.
suff -> : i == Ordinal x'_m; last by apply/eqP; apply: val_inj => /=; rewrite x_i.
by rewrite /= mulVf // oner_eq0.
Qed.

(*  GG -- giving up for now --
Lemma pick_enum_rank : forall (T : finType) (p : pred T) x,
 pick p = Some x -> pred0b [pred y | (enum_rank y < enum_rank x) && p y].
Proof.
move=> T p x; rewrite /pick /enum -enumE /enum_rank /=.
have : x \in (enum T) by rewrite mem_enum.
elim: (enum T) (enum_uniq T) => //= x' s Rs; case/andP => x'_s Us.
rewrite in_cons; case/orP; case: ifP => //.
- by move=> _; move/eqP=> -> _; rewrite eq_refl /=; apply/pred0P.
- by move=> _; move/eqP=> -> _; rewrite eq_refl /=; apply/pred0P.
- by move=> _ _ [] ->; rewrite eq_refl /=; apply/pred0P.
move=> px' x_s H; apply/pred0P => y /=.
case: ifP => [|_]; first by move/eqP<-; rewrite px' andbF.
case: ifP => [|_]; first by move/eqP => H'; rewrite H' x_s in x'_s.
by move: (Rs Us x_s H); move/pred0P; move/(_ y) => /=; rewrite -(ltn_add2r 1) 2!addn1.
Qed.

Lemma pivot_nz_le0 : forall A i j,
 if (pivot_nz A i j) is Some l then (forallb k : 'I_n, (k < l) ==> (A i k == 0))
 else true.
Proof.
move=> A i j; rewrite /pivot_nz.
move: (@pick_enum_rank _ [pred l | (A i l != 0) && (l < j)]).
case: pickP => [k /=|//]; case/andP => Aik k_j; move/(_ k (eqP (eq_refl _))).
move/pred0P => P0; apply/forallP => k'; apply/implyP => k'_k;move: (P0 k').
by rewrite /= (ltn_trans k'_k k_j) andbT !index_enum_ord k'_k /=; move/negPn.
Qed.

Lemma pivot_nz_first : forall A i j,pivot_nz (rref_step A j).2 i j ->
 pivot_nz (rref_step A j.+1).2 i j.+1 = pivot_nz (rref_step A j).2 i j.
Proof.
move=> A i j.
case: (leqP n j) => n_j.
  have -> : (rref_step A j.+1) = (rref_step A j).
    by rewrite /rref_step !take_oversize 1?size_enum_ord // (leq_trans n_j) // ltnW.
  rewrite /pivot_nz => _; apply: eq_pick => k /=; congr (_ && _).
  apply/idP/idP; last by move/ltn_trans; move/(_ _ (ltnSn j)).
  by move=> _; apply: (leq_trans _ n_j).
move: (pivot_nz_le0 (rref_step A j.+1).2 i j.+1).
move: (pivot_nz_le0 (rref_step A j).2 i j).
rewrite /pivot_nz; case: pickP => /= [k /=|//]; case: pickP => // [k' /=|]; last first.
  move/(_ k) => /= Hl; case/andP => Aik k_j _; move: Aik.
  by rewrite rref_step_col (ltn_trans k_j) // andbT in Hl; rewrite rref_step_col // Hl.
case/andP=> Aik' k'_j; case/andP=> Aik k_j H1 H2 _.
case: (ltngtP k' k); last by move=> *; congr Some; apply: val_inj => /=.
  move=> k'_k; move/forallP: H1; move/(_ k'); rewrite k'_k /=; move: Aik'.
  by rewrite rref_step_col // (rref_step_col _ (ltn_trans k'_k k_j)); move/negbTE->.
move=> k_k'; move/forallP: H2; move/(_ k); rewrite k_k' /=; move: Aik.
by rewrite rref_step_col // (rref_step_col _ (ltn_trans k_j (ltnSn j))); move/negbTE->.
Qed.

Lemma all_zero_row_in_bottom_step : forall A j,
 all_zero_row_in_bottom (rref_step A j).2 j.
Proof.
move=> A j; apply/forallP=> i; apply/implyP => Zri; apply/forallP => k.
apply/implyP => ik; apply/forallP => j'; apply/implyP => j'j; apply/eqP.
by apply: rref_step_nil_mx => //; apply: (leq_trans _ ik); apply: zrow_in_bottom.
Qed.

Lemma pivot_nz_eq1_step : forall A j, pivot_nz_eq1 (rref_step A j).2 j.
Proof.
move=> A; elim=> // [|j Rj]; apply/forallP => i; rewrite /pivot_nz.
  by case: pickP => /= [x| _]; [rewrite ltn0 andbF | apply/forallP].
case: (leqP n j) => n_j.
  have -> : (rref_step A j.+1) = (rref_step A j).
    by rewrite /rref_step !take_oversize 1?size_enum_ord // ?(leq_trans n_j).
  have Hp : [pred l | ((rref_step A j).2 i l != 0) && (l < j.+1)] =1
            [pred l | ((rref_step A j).2 i l != 0) && (l < j)]. 
    by move=> k /= ; rewrite (leq_trans _ n_j) // (leq_trans _ (leq_trans n_j _)).
  have -> : z_row (rref_step A j).2 i j.+1 = z_row (rref_step A j).2 i j.
    apply/idP/idP; move/forallP => Ht; apply/forallP => k; apply/implyP => Hk.
    - by move: (Ht k); move/implyP=> -> //; apply: (leq_trans _ (leq_trans n_j _)).
    by move: (Ht k); move/implyP=> -> //; apply: (leq_trans _ n_j).
  by rewrite (eq_pick Hp); move/forallP: Rj; move/(_ i).
move/forallP: Rj; move/(_ i); rewrite -/(pivot_nz (rref_step A j.+1).2 i j.+1).
move: (@pivot_nz_first A i j).
rewrite {1 3 4}/pivot_nz; case: pickP => [k /=|].
  case/andP => H1 H2; move/(_ is_true_true)=> -> H3; apply/eqP.
  rewrite /rref_step (take_nth (Ordinal n_j)) 1?size_enum_ord // -cats1 foldl_cat.
  rewrite -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /= /rref_fun.
  case: insubP => //= [[] [] /= _ _ x_m _ _|]; last by rewrite (eqP H3).
  case: pickP => [k' /=|]; last by rewrite (eqP H3).
  case/andP; rewrite annihilate_colE !mxE eq_refl /=; move/eqP => Akk' x_k.
  case: ifP => /= H4; last move/negPn: H4 => H4; rewrite 1?H4; last first.
  - rewrite rref_step_nil_mx 1?eq_refl // in H1.
    by move/eqP: H4; move/(congr1 (@nat_of_ord m)) => /= <-.
  rewrite (negbTE H4) mulfV // invf1 !mulr1 //; case: ifP => H5; rewrite H5.
  - by rewrite rref_step_nil_mx 1?eq_refl // in H1; rewrite (eqP H5).
  by rewrite (@rref_step_nil_mx _ k' k) // !mulr0 oppr0 addr0 (eqP H3).
move=> H1 _ Zri; rewrite /pivot_nz.
suff : [pred k | ((rref_step A j.+1).2 i k != 0) && (k < j.+1)] =1
       [pred k | ((rref_step A j.+1).2 i k != 0) && (k == j :> nat)].
  move/eq_pick ->; case: pickP => [k /=|]; first case/andP => Aik k_j; last first.
  - move/(_ (Ordinal n_j)) => /=; rewrite eq_refl andbT; move/negPn => Aij.
    apply/forallP => k; apply/implyP; rewrite ltnS leq_eqVlt.
    case/orP => k_j; first move/eqP: k_j => k_j.
    - by rewrite -(eqP Aij); apply/eqP; congr fun_of_matrix; apply: val_inj.
    move/forallP: Zri; move/(_ k); move/implyP; move/(_ k_j); move/eqP<-.
    by rewrite rref_step_col 1?(ltn_trans k_j _) // (rref_step_col _ k_j).
  have x_i : (rref_step A j).1 <= i by apply: zrow_in_bottom.
  have {k_j}k_j : k = (Ordinal n_j) by apply: ord_inj => /=; rewrite (eqP k_j).
  move: Aik; rewrite /rref_step (take_nth k) 1?size_enum_ord // -cats1 foldl_cat.
  rewrite -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) -k_j /= /rref_fun.
  case: insubP => //= [[] [] /= _ _ x_m _ _|]; last first.
  - by rewrite (leq_ltn_trans x_i (ltn_ord _)).
  case: pickP => [k' /=|]; last by move/(_ i) => /=; rewrite x_i andbT => ->.
  case/andP; move/eqP => Ak'k x_k'; rewrite annihilate_colE !mxE eq_refl /=.
  case: ifP => /= H2; last by move/negPn: H2 => H2; rewrite 1?H2 mulfV.
  by rewrite (negbTE H2); rewrite mulfV // invf1 !mulr1 // addrN eq_refl.
move=> k /=; rewrite ltnS leq_eqVlt andb_orr -{2}(orbF (_  && (k == j :> nat))).
congr (_ || _); rewrite -(H1 k) /=; case k_j : (k < j); last by rewrite !andbF.
by rewrite !andbT rref_step_col 1?(ltn_trans k_j _) // (rref_step_col _ k_j).
Qed.

Lemma pivot_nz_zcol_step : forall A j, pivot_nz_zcol (rref_step A j).2 j.
Proof.
move=> A; elim=> //= [|j Rj]; apply/forallP => i; first rewrite /pivot_nz.
  by case: pickP => // k /=; rewrite ltn0 andbF.
move/forallP: Rj; move/(_ i); case: (leqP n j) => n_j.
  have -> : (rref_step A j.+1) = (rref_step A j).
    by rewrite /rref_step !take_oversize 1?size_enum_ord // ?(leq_trans n_j).
  rewrite /pivot_nz.
  suff : [pred l | ((rref_step A j).2 i l != 0) && (l < j)] =1
         [pred l | ((rref_step A j).2 i l != 0) && (l < j.+1)].
    by move/eq_pick<-.
  by move=> k /= ; rewrite (leq_trans _ n_j) // (leq_trans _ (leq_trans n_j _)).
move: (@pivot_nz_first A i j);  rewrite /pivot_nz.
case: pickP => [k /=|]; case: pickP => // k' /=.
  case/andP => Aik' k'j; case/andP => Aik kj; move/(_ is_true_true) => [] -> P0.
  apply/forallP => i'; apply/implyP => i'i; move/forallP: P0; move/(_ i').
  by rewrite i'i /= rref_step_col // (rref_step_col _ (ltn_trans kj (ltnSn j))).
case/andP => Aik k'j P0 _ _; apply/forallP => i'; apply/implyP => i'i.
have x_i : (rref_step A j).1 <= i.
  apply: zrow_in_bottom; apply/forallP => j'; apply/implyP=> j'j.
  by move: (P0 j') => /=; rewrite j'j andbT; move/negPn.
move: Aik; rewrite /rref_step (take_nth k') 1?size_enum_ord // -cats1 foldl_cat.
rewrite -/(rref_step A j) (nth_ord_enum _ (Ordinal n_j)) /= /rref_fun.
case: insubP => //= [[] [] /= _ _ x_m _ _|]; last first.
  by rewrite (leq_ltn_trans x_i (ltn_ord _)).
case: pickP => [k /=|]; last (move/(_ i) => /=; rewrite x_i andbT); last first.
  case k'_j: (k' == (Ordinal n_j)); first by move/eqP: k'_j => -> ->.
  move=> _; rewrite (@rref_step_nil_mx _ i k') 1?eq_refl //.
  rewrite ltnS leq_eqVlt in k'j; case/orP: k'j => // k'j; move/negP: k'_j => [].
  by apply/eqP; apply: ord_inj => /=; rewrite (eqP k'j).
case/andP; move/eqP => Akj x_k; rewrite !annihilate_colE !mxE eq_refl.
case: ifP => /= H1; last move/negPn: H1 => H1; rewrite 1?H1 1?(negbTE H1).
  rewrite mulfV // invf1 !mulr1; rewrite ltnS leq_eqVlt in k'j.
  case/orP: k'j => k'j; first suff -> : k' = Ordinal n_j.
  - by rewrite mulfV // mulr1 addrN eq_refl.
  - by apply: val_inj => /=; rewrite (eqP k'j).
  rewrite (@rref_step_nil_mx _ k k') // !mulr0 oppr0 addr0.
  by rewrite 2?(@rref_step_nil_mx _ _ k') // if_same eq_refl.
rewrite -(eqP H1) (negbTE i'i) /= mulfV // invf1 !mulr1.
rewrite ltnS leq_eqVlt in k'j; case/orP: k'j => k'j; last first.
  by rewrite (@rref_step_nil_mx _ _ k') // mulr0 eq_refl.
suff -> : k' = Ordinal n_j; last by apply: val_inj => /=; rewrite (eqP k'j).
by rewrite mulfV // mulr1 addrN.
Qed.

Lemma pivot_mono_step : forall A j, pivot_mono (rref_step A j).2 j.
Proof.
move=> A j; apply/forallP => i1.
move: (pivot_nz_le0 (rref_step A j).2 i1 j); rewrite {1 2}/pivot_nz.
case: pickP => // k /=; case/andP => Ai1k kj P0.
have {P0}Zri1 : z_row (rref_step A k).2 i1 k.
  apply/forallP => k'; apply/implyP => k'k; move/forallP: P0; move/(_ k').
  rewrite k'k /= rref_step_col 1?(ltn_trans k'k kj) //; move/eqP<-.
  by rewrite rref_step_col.
apply/forallP => i2; move: (pivot_nz_le0 (rref_step A j).2 i2 j).
rewrite /pivot_nz; case: pickP => // k' /=; case/andP => Ai2k k'j P0.
have {P0}Zri2 : z_row (rref_step A k').2 i2 k'.
  apply/forallP => l; apply/implyP => lk'; move/forallP: P0; move/(_ l).
  rewrite lk' /= rref_step_col 1?(ltn_trans lk' k'j) //; move/eqP<-.
  by rewrite rref_step_col.
apply/implyP => i1i2; case: (ltngtP k k') => // k'k.
  move/forallP: (all_zero_row_in_bottom_step A k); move/(_ i1).
  rewrite Zri1 /=; move/forallP; move/(_ i2); rewrite (ltnW i1i2) /=.
  move/forallP; move/(_ k'); rewrite k'k /= rref_step_col //; move: Ai2k.
  by rewrite rref_step_col //; move/negbTE->.
rewrite -(negbTE Ai2k) rref_step_col //.
suff <- : k = k' :> 'I_n; first apply/eqP; last by apply: val_inj.
apply: rref_step_nil_mx => //; apply: (leq_trans (rref_step_rank_leS A k)).
by apply: (leq_ltn_trans _ i1i2); apply: zrow_in_bottom.
Qed.
 *)
End InvariantsLemmas.
(*
Lemma is_rref_rref : forall A, is_rref (rref_mx A).
Proof.
move=> A; rewrite /is_rref all_zero_row_in_bottom_step pivot_nz_eq1_step.
by rewrite pivot_nz_zcol_step pivot_mono_step.
Qed.

Lemma leq_rank : forall A, rank A <= minn m n.
Proof. by move=> A; rewrite leq_minr rank_le_col rank_le_row. Qed.
*)
End GaussianElimination.