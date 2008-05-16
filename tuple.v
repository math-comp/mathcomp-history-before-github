Require Import ssreflect.
Require Import seq.
Require Import eqtype.
Require Import ssrnat.
Require Import ssrfun.
Require Import ssrbool.
Require Import fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Def.

Variables (n : nat) (T : Type).

Record tuple_repr : Type :=
  TupleRepr {tuple_val :> seq T; _ : size tuple_val == n}.

Definition tuple : predArgType := tuple_repr.
Identity Coercion repr_of_tuple : tuple >-> tuple_repr.
Definition Tuple : forall s : seq T, size s == n -> tuple := TupleRepr.

Canonical Structure tuple_subType :=
  @SubType _ _ tuple tuple_val Tuple tuple_repr_rect vrefl.

Canonical Structure tuple_repr_subType :=
  SubType tuple_val tuple_repr_rect vrefl.

Lemma size_tuple : forall t : tuple, size t = n.
Proof. move=> f; exact: (eqP (valP f)). Qed.

Lemma tsub_default : forall (t : tuple) (i : I_(n)), T.
Proof. by case=> [[|//]]; move/eqP <-; case. Qed.

Definition tsub t i := sub (tsub_default t i) t i.

Lemma tsub_sub : forall x t i, tsub t i = sub x t i.
Proof. by move=> x t i; apply: set_sub_default; rewrite size_tuple. Qed.

Lemma maps_tsub_enum : forall t, maps (tsub t) (enum {I_(n)}) = t.
Proof.
move=> t; case def_t: {-}(val t) => [|x0 t'].
  suffices: #|{I_(n)}| = 0 by rewrite cardE; move/size_eq0->.
  by rewrite card_ord -(size_tuple t) def_t.
apply: (@eq_from_sub _ x0) => [|i]; rewrite size_maps.
  by rewrite -cardE size_tuple card_ord.
move=> lt_i_e; have lt_i_n: i < n by rewrite -[n]card_ord cardE.
by rewrite (sub_maps (Ordinal lt_i_n)) // (tsub_sub x0) sub_enum_ord.
Qed.

Lemma eq_from_tsub : forall t1 t2, tsub t1 =1 tsub t2 -> t1 = t2.
Proof.
by move=> *; apply: val_inj; rewrite /= -!maps_tsub_enum; exact: eq_maps.
Qed.

Definition tuple_of (t : tuple) s of phantom (seq T) t -> phantom (seq T) s :=
  t.

End Def.

Notation "[ 'tuple' 'of' s ]" := (@tuple_of _ _ _ s id)
  (at level 0, format "[ 'tuple'  'of'  s ]") : form_scope.

Definition tsize n T (t : tuple n T) := nosimpl size t.

Notation "[ 'tsub' t i ]" := (tsub t (@Ordinal (tsize t) i (erefl true)))
  (at level 0, t, i at level 8, format "[ 'tsub'  t  i ]") : form_scope.

Canonical Structure seq0_tuple T :=
   Tuple (erefl _ : @size T [::] == 0).
Canonical Structure adds_tuple n T x (t : tuple n T) :=
   Tuple (valP t : size (x :: t) == n.+1).

Notation "[ 'tuple' x1 ; .. ; xn ]" := [tuple of x1 :: .. [:: xn] ..]
  (at level 0, format "[ 'tuple' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

Notation "[ 'tuple' ]" := [tuple of [::]]
  (at level 0, format "[ 'tuple' ]") : form_scope.

Section SeqTuple.

Variables (n : nat) (T rT : Type).
Notation tT := (tuple n T).

Lemma seqn_tupleP : forall x : T, size (seqn n x) == n.
Proof. by move=> x; rewrite size_seqn. Qed.
Canonical Structure seqn_tuple x := Tuple (seqn_tupleP x).

Lemma iota_tupleP : forall m, size (iota m n) == n.
Proof. by move=> m; rewrite size_iota. Qed.
Canonical Structure iota_tuple m := Tuple (iota_tupleP m).

Lemma behead_tupleP : forall t : tT, size (behead t) == n.-1.
Proof. by move=> t; rewrite size_behead size_tuple. Qed.
Canonical Structure behead_tuple t := Tuple (behead_tupleP t).

Lemma belast_tupleP : forall x (t : tT), size (belast x t) == n.
Proof. by move=> x t; rewrite size_belast size_tuple. Qed.
Canonical Structure belast_tuple x t := Tuple (belast_tupleP x t).

Lemma cat_tupleP : forall n1 n2 (t1 : tuple n1 T) (t2 : tuple n2 T),
  size (t1 ++ t2) == n1 + n2.
Proof. by move=> n1 n2 t1 t2; rewrite size_cat !size_tuple. Qed.
Canonical Structure cat_tuple n1 n2 t1 t2 := Tuple (@cat_tupleP n1 n2 t1 t2).

Lemma take_tupleP : forall m (t : tT), size (take m t) == minn m n.
Proof. by move=> m t; rewrite size_take size_tuple eqxx. Qed.
Canonical Structure take_tuple m t := Tuple (take_tupleP m t).

Lemma drop_tupleP : forall m (t : tT), size (drop m t) == n - m.
Proof. by move=> m t; rewrite size_drop size_tuple. Qed.
Canonical Structure drop_tuple m t := Tuple (drop_tupleP m t).

Lemma rev_tupleP : forall t : tT, size (rev t) == n.
Proof. by move=> t; rewrite size_rev size_tuple. Qed.
Canonical Structure rev_tuple t := Tuple (rev_tupleP t).

Lemma rot_tupleP : forall m (t : tT), size (rot m t) == n.
Proof. by move=> m t; rewrite size_rot size_tuple. Qed.
Canonical Structure rot_tuple m t := Tuple (rot_tupleP m t).

Lemma rotr_tupleP : forall m (t : tT), size (rotr m t) == n.
Proof. by move=> m t; rewrite size_rotr size_tuple. Qed.
Canonical Structure rotr_tuple m t := Tuple (rotr_tupleP m t).

Lemma maps_tupleP : forall f (t : tT), @size rT (maps f t) == n.
Proof. by move=> f t; rewrite size_maps size_tuple. Qed.
Canonical Structure maps_tuple f t := Tuple (maps_tupleP f t).

Lemma scanl_tupleP : forall f x (t : tT), @size rT (scanl f x t) == n.
Proof. by move=> f x t; rewrite size_scanl size_tuple. Qed.
Canonical Structure scanl_tuple f x t := Tuple (scanl_tupleP f x t).

Lemma pairmap_tupleP : forall f x (t : tT), @size rT (pairmap f x t) == n.
Proof. by move=> f x t; rewrite size_pairmap size_tuple. Qed.
Canonical Structure pairmap_tuple f x t := Tuple (pairmap_tupleP f x t).

Lemma zip_tupleP : forall t1 t2 : tT, size (zip t1 t2) == n.
Proof. by move=> *; rewrite size1_zip !size_tuple. Qed.
Canonical Structure zip_tuple t1 t2 := Tuple (zip_tupleP t1 t2).

Definition thead (n : pos_nat) (t : tuple n T) := tsub t ord0.

Lemma tsub0 : forall x n (t : tuple n T), tsub [tuple of x :: t] ord0 = x.
Proof. by []. Qed.

Lemma theadE : forall x n (t : tuple n T), thead [tuple of x :: t] = x.
Proof. by []. Qed.

Lemma tuple0 : forall t : tuple 0 T, t = [tuple].
Proof. by move=> t; apply: val_inj; case: t => [[]]. Qed.

CoInductive tuple1_spec : tuple n.+1 T -> Type :=
  Tuple1spec x (t : tT) : tuple1_spec [tuple of x :: t].

Lemma tupleP : forall t, tuple1_spec t.
Proof.
move=> [[|x t] //= sz_t]; pose t' := Tuple (sz_t : size t == n).
rewrite (_ : TupleRepr _ = [tuple of x :: t']) //; exact: val_inj.
Qed.

Lemma tsub_maps : forall f (t : tT) i,
  tsub [tuple of maps f t] i = f (tsub t i) :> rT.
Proof. by move=> f t i; apply: sub_maps; rewrite size_tuple. Qed.

End SeqTuple.

Lemma tsub_behead : forall (n : pos_nat) T (t : tuple n.+1 T) i,
  tsub [tuple of behead t] i = tsub t (inord i.+1).
Proof.
by move=> n T; case/tupleP=> x t i; rewrite !(tsub_sub x) inordK ?ltnS.
Qed.

Lemma tuple_eta : forall n T (t : tuple n.+1 T),
  t = [tuple of thead t :: behead t].
Proof. move=> n T; case/tupleP=> x t; exact: val_inj. Qed.

Section EqTuple.

Variables (n : nat) (T : eqType).

Canonical Structure tuple_repr_eqType :=
  Eval hnf in [subEqType for @tuple_val n T].
Canonical Structure tuple_eqType := Eval hnf in [eqType of tuple n T].

Canonical Structure tuple_predType :=
  Eval hnf in mkPredType (fun t : tuple n T => mem_seq t).

Canonical Structure tuple_repr_predType :=
  Eval hnf in mkPredType (fun t : tuple_repr n T => mem_seq t).

Lemma memtE : forall t : tuple n T, mem t = mem (tuple_val t).
Proof. by []. Qed.

End EqTuple.

Section FinTuple.

Variables (n : nat) (T : finType).
Notation tT := (tuple n T).

Lemma tuple_enum : {enumMixin tT}.
Proof.
elim: n => [|m [et cnt_et]].
  by exists [:: ([tuple] : tuple 0 T)] => t; rewrite /= [t]tuple0.
exists (foldr (fun x => cat (maps (adds_tuple x) et)) [::] (enum T)).
case/tupleP=> x t; rewrite -[1]/(x \in T : nat) -(mem_enum T).
elim: (enum T) (uniq_enum T) => //= y e IHe; case/andP=> ney.
rewrite count_cat count_maps in_adds; move/IHe->.
rewrite -[preim _ _]/[fun t' => (y == x) && (t' == t)] /= eq_sym.
by move/negPf: ney; case: eqP => [-> -> | _ _]; rewrite (cnt_et, count_pred0).
Qed.

Definition tuple_finMixin := @FinMixin tT _ tuple_enum.
Canonical Structure tuple_finType := FinClass tuple_finMixin.
Canonical Structure tuple_subFinType := SubFinType tuple_finMixin.

Definition tuple_repr_finMixin := @FinMixin (tuple_repr n T) _ tuple_enum.
Canonical Structure tuple_repr_finType := FinClass tuple_repr_finMixin.
Canonical Structure tuple_repr_subFinType := SubFinType tuple_repr_finMixin.

Lemma enum_tupleP : forall a : pred T, size (enum a) == #|a|.
Proof. by move=> a; rewrite -cardE. Qed.
Canonical Structure enum_tuple a := Tuple (enum_tupleP a).

Definition ord_tuple : tuple n I_(n) := Tuple (introT eqP (size_enum_ord n)).
Lemma val_ord_tuple : val ord_tuple = enum {I_(n)}. Proof. by []. Qed.

Lemma tuple_maps_ord : forall T' (t : tuple n T'),
  t = [tuple of maps (tsub t) ord_tuple].
Proof. by move=> T' t; apply: val_inj => /=; rewrite maps_tsub_enum. Qed.

End FinTuple.


