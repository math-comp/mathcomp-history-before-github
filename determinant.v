Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple.
Require Import div groups group_perm zp signperm indexed_products.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* More nat notation (frees the S symbol) *)

Notation "0" := 0 (at level 0) : dnat_scope.
Notation "n '`+1'" := (S n) (at level 9, format "n '`+1'") : dnat_scope.
Notation "n '`-1'" := (pred n) (at level 9, format "n '`-1'") : dnat_scope.

Delimit Scope local_scope with loc.
Open Scope local_scope.

(* More funs variants : local equality, cancellation, bijection. *)

Definition dfequal A B (a : set A) (f f' : A -> B) :=
  forall x, a x -> f x = f' x.

Definition dcancel A B (a : set A) (f : A -> B) f' :=
  forall x, a x -> f' (f x) = x.

Lemma dcan_inj : forall (A B : eqType) a f f',
  @dcancel A B a f f' -> dinjective a f.
Proof.
by move=> A B a f f' fK x y; do 2![move/fK=> Dx; rewrite -{2}Dx {Dx}] => ->.
Qed.

Definition icancel A B (b : set B) (f : A -> B) f' :=
  forall x, b (f x) -> f' (f x) = x.

Definition dbijective A B (a : set A) (f : A -> B) :=
  exists2 f', dcancel a f f' & icancel a f' f.

(* Used for the assumption of reindex_sum below. *)
Definition ibijective A B (b : set B) (f : A -> B) :=
  exists2 f', icancel b f f' & dcancel b f' f.

(* Complements for eqtype. *)

Lemma insubT : forall d (a : set d) x (ax : a x),
  insub a x = Some (EqSig a x ax).
Proof.
move=> d a x ax.
by case: insubP=> [[y ay] _ Exy| ]; [congr Some; exact: val_inj | rewrite ax].
Qed.

Implicit Arguments insubT [d x].

Lemma insub_val : forall d a u, @insub d a (val u) = Some u.
Proof. by move=> d a [x Hx]; rewrite -insubT. Qed.

Lemma insubF : forall d (a : set d) x, a x = false -> insub a x = None.
Proof. by move=> d a x Hx; case: insubP=> // ?; rewrite Hx. Qed.

Lemma insubN : forall d (a : set d) x, ~~ a x -> insub a x = None.
Proof. move=> d a x; move/negbET; exact: insubF. Qed.

(* Supplementary material for ordinals, for use as array indices.     *)
(* Ordinals should really be a proper type, and coerce to nat; at the *)
(* Very least, ordinal n should be the eq_sig, not the finType.       *)

(* More compact notations for the (fin)Types for index ranges, and    *)
(* and their permutation group and function space.                    *)
(*  We'd preferred to use LaTeX-style curly braces for the indices,   *)
(* however the Coq Notation hacks to circumvent camlp4 limitations    *)
(* for the { _ } + { _ } notation makes this impossible.              *)

Notation "'I_' ( n )" := (ordinal n)
  (at level 0, format "'I_' ( n )") : local_scope.
Notation "'S_' ( n )" := (permType I_(n))
  (at level 0, format "'S_' ( n )") : local_scope.
Notation "'F_' ( n )" := (fgraphType I_(n) I_(n))
  (at level 0, format "'F_' ( n )") : local_scope.

Definition ord0 : ordinal 1 := make_ord (ltnSn 0).

(* The integer bump / unbump operations, stolen from the PoplMark file! *)

Definition bump h i := (h <= i) + i.
Definition unbump h i := i - (h < i).

Lemma bumpK : forall h, cancel (bump h) (unbump h).
Proof.
rewrite /bump /unbump => h i; case: (leqP h i) => Hhi.
  by rewrite ltnS Hhi subn1.
by rewrite ltnNge ltnW ?subn0.
Qed.

Lemma neq_bump : forall h i, h != bump h i.
Proof.
move=> h i; rewrite /bump eqn_leq.
by case: (leqP h i) => Hhi; [rewrite ltnNge Hhi andbF | rewrite leqNgt Hhi].
Qed.

Lemma unbumpK : forall h, dcancel (setC1 h) (unbump h) (bump h).
Proof.
rewrite /bump /unbump => h i; move/eqP=> Dhi.
case: (ltngtP h i) => // Hhi; last by rewrite subn0 leqNgt Hhi.
by rewrite -ltnS subn1 (ltnSpred Hhi) Hhi add1n (ltnSpred Hhi).
Qed.

(* The lift operations on ordinals; to avoid a messy dependent type, *)
(* unlift is a partial operation (returns an option).                *)

Lemma lift_subproof : forall n h (i : I_(n`-1)), bump h (val i) < n.
Proof.
by case=> [|n] h [i //= Hi]; rewrite /bump; case: (h <= _); last exact: ltnW.
Qed.

Definition lift n (h : I_(n)) (i : I_(n`-1)) :=
  make_ord (lift_subproof (val h) i).

Lemma unlift_subproof : forall n (h : I_(n)) (u : eq_sig (setC1 h)),
  unbump (val h) (val (val u)) < pred n.
Proof.
move=> n h [i] /=; move/unbumpK => Di.
have lti := valP i; rewrite -ltnS (ltnSpred lti).
move: lti; rewrite -{1}Di; move: {i Di} (unbump _ _) => m.
rewrite /bump; case: (leqP _ m) => // Hm _; exact: leq_trans (valP h).
Qed.

Definition unlift n (h i : I_(n)) :=
  if insub (setC1 h) i is Some u then
    Some (make_ord (unlift_subproof u))
  else None.

CoInductive unlift_spec n (h i : I_(n)) : option I_(n`-1) -> Type :=
  | UnliftSome j of i = lift h j : unlift_spec h i (Some j)
  | UnliftNone   of i = h        : unlift_spec h i None.

Lemma unliftP : forall n (h i : I_(n)), unlift_spec h i (unlift h i).
Proof.
move=> n h i; rewrite /unlift; case: insubP => [u Hi Di | Di]; constructor.
  by apply: val_inj; rewrite /= Di (unbumpK Hi).
by rewrite negbK in Di; move/eqP: Di.
Qed.

Lemma neq_lift : forall n (h : I_(n)) i, h != lift h i.
Proof. by move=> n h i; exact: neq_bump. Qed.

Lemma unlift_none : forall n (h : I_(n)), unlift h h = None.
Proof. by move=> n h; case: unliftP => // j Dh; case/eqP: (neq_lift h j). Qed.

Lemma unlift_some : forall n (h i : I_(n)),
  h != i -> {j | i = lift h j & unlift h i = Some j}.
Proof.
move=> n h i; rewrite eq_sym; move/eqP=> Hi.
by case Dui: (unlift h i) / (unliftP h i) => [j Dh|//]; exists j.
Qed.

Lemma lift_inj : forall n (h : I_(n)), injective (lift h).
Proof.
move=> n h i1 i2; move/eqP.
by rewrite -val_eqE (eqtype.can_eq (@bumpK _)) val_eqE; move/eqP.
Qed.

Lemma liftK : forall n (h : I_(n)) i, unlift h (lift h i) = Some i.
Proof.
by move=> n h i; case: (unlift_some (neq_lift h i)) => j; move/lift_inj->.
Qed.

(* Shifting and splitting indices, for cutting and pasting arrays *)

Lemma lshift_subproof : forall m n (i : I_(m)), val i < m + n.
Proof. move=> m n i; exact: leq_trans (valP i) (leq_addr _ _). Qed.

Lemma rshift_subproof : forall m n (i : I_(n)), m + val i < m + n.
Proof. by move=> m n i; rewrite ltn_add2l ordinal_ltn. Qed.

Definition lshift m n (i : I_(m)) := make_ord (lshift_subproof n i).
Definition rshift m n (i : I_(n)) := make_ord (rshift_subproof m i).

Lemma split_subproof : forall m n (i : I_(m + n)),
  val i >= m -> val i - m < n.
Proof. by move=> m n i; move/leq_subS <-; rewrite leq_sub_add ordinal_ltn. Qed.

Definition split m n (i : I_(m + n)) : I_(m) + I_(n) :=
  match ltnP (val i) m with
  | LtnNotGeq Hi =>  inl _ (make_ord Hi)
  | GeqNotLtn Hi =>  inr _ (make_ord (split_subproof Hi))
  end.

CoInductive split_spec m n (i : I_(m + n)) : I_(m) + I_(n) -> bool -> Type :=
  | SplitLo (j : I_(m)) & val i = val j     : split_spec i (inl _ j) true
  | SplitHi (k : I_(n)) & val i = m + val k : split_spec i (inr _ k) false.

Lemma splitP : forall m n i, @split_spec m n i (split i) (val i < m).
Proof.
rewrite /split {3 6}/leq => m n i; case: ltnP => Hi; first exact: SplitLo.
by apply: SplitHi; rewrite //= leq_add_sub.
Qed.

Definition unsplit m n (si : I_(m) + I_(n)) :=
  match si with inl i => lshift n i | inr i => rshift m i end.

Coercion isleft A B (u : A + B) := if u is inl _ then true else false.

Lemma ltn_unsplit : forall m n si, val (@unsplit m n si) < m = si.
Proof. by move=> m n [] i /=; rewrite ?(valP i) // ltnNge leq_addr. Qed.

Lemma splitK : forall m n, cancel (@split m n) (@unsplit m n).
Proof. by move=> m n i; apply: val_inj; case: splitP. Qed.

Lemma unsplitK : forall m n, cancel (@unsplit m n) (@split m n).
Proof.
move=> m n si.
case: splitP (ltn_unsplit si); case: si => //= i j; last move/addn_injl;
  by move/val_inj->.
Qed.

Section determinant_context.

(* Ring theory; should be replaced by a common structure like RingTheory. *)

Variable R : Type.
Variables plus mult : R -> R -> R.
Variable opp : R -> R.
Variables zero one : R.

Notation "x + y" := (plus x y) : local_scope.
Notation "- y" := (opp y) : local_scope.
Notation "x * y" := (mult x y) : local_scope.
Notation "1" := one (at level 0) : local_scope.
Notation "0" := zero (at level 0): local_scope.
Notation "- 1" := (- 1) (at level 0) : local_scope.
Notation "x - y" := (x + (- y)) : local_scope.

(* Injecting natural integers. *)

Definition RofSn n := iter n (fun x => x + 1) 1.

Coercion R_of_nat n := if n is n'`+1 then RofSn n' else 0.

(* We'll show later RofSnE : forall n, RofSn n = n + 1. *)

(* Integer powers. *)

Definition RexpSn x n := iter n (fun y => y * x) x.

Definition Rexp_nat x n := if n is n'`+1 then RexpSn x n' else 1.

Notation "x ^ n" := (Rexp_nat x n) : local_scope.

(* We'll show later RexpSnE : forall x n, RexpSn x n = x ^ n * x *)

(* Importing indexed sums, with some user-friendly notation. *)
(* Unfortunately, and as usual, we can't package any of this *)
(* using modules, because of the dependency on section ring  *)
(* parameters. We might have a way out with canonical        *)
(* structures, though.                                       *)

Implicit Arguments iprod [R d].

(* There's no good way to define prefix operators with Coq notations,  *)
(* without triggering some bug in camlp4 or the Coq pretty-printer.    *)
(* If they both implemented precedence grammars correctly, we would    *)
(* define them with very high left precedence, and moderate (35 to 40) *)
(* right precedence; unfortunately, the Coq pretty-printer doesn't     *)
(* understand this, and produces very confusing output as a result.    *)
(*   Therefore, we use the same left and right priorities, which ought *)
(* to mean that the parens are needed in x * (\sum_(i) f i). A bug (or *)
(* feature?) of camlP4 allows to omit them, however. Alas, this        *)
(* loophole also ignores the declared right priority of \sum, so that  *)
(* x * \sum_(i) f i = 0 is parsed as x * (\sum f i = 0).               *)
(*  The latter is always a type error, so this is the lesser of two    *)
(* evils, and we take this option.                                     *)
(*  Note that, consistent with math conventions, \sum is tighter than  *)
(* addition, and \prod tighter than multiplication.                    *)

Notation "'\sum_' ( 'in' r ) F" := (iprod plus 0 r F)
   (at level 40, F at level 40,
   format "'\sum_' ( 'in'  r )  F") : local_scope.
Notation "'\prod_' ( 'in' r ) F" := (iprod mult 1 r F)
   (at level 35, F at level 35,
   format "'\prod_' ( 'in'  r )  F") : local_scope.

Notation "'\sum_' () F" := (iprod plus 0 (setA _) F)
   (at level 40, F at level 40, format "'\sum_' ()  F") : local_scope.
Notation "'\prod_' () F" := (iprod mult 1 (setA _) F)
   (at level 35, F at level 35, format "'\prod_' () F") : local_scope.

Notation "'\sum_' ( i 'in' r ) E" := (iprod plus 0 r (fun i => E))
   (at level 40, E at level 40, i at level 50,
    format "'\sum_' ( i  'in'  r )  E") : local_scope.
Notation "'\prod_' ( i 'in' r ) E" := (iprod mult 1 r (fun i => E))
   (at level 35, E at level 35, i at level 50,
    format "'\prod_' ( i  'in'  r )  E") : local_scope.

Notation "'\sum_' ( i : t 'in' r ) E" := (iprod plus 0 r (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t 'in' r ) E" := (iprod mult 1 r (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i | P ) E" := (iprod plus 0 (fun i => P) (fun i => E))
   (at level 40, E at level 40, i at level 50, 
   format "'\sum_' ( i  |  P )  E") : local_scope.
Notation "'\prod_' ( i | P ) E" := (iprod mult 1 (fun i => P) (fun i => E))
   (at level 35, E at level 35, i at level 50,
   format "'\prod_' ( i  |  P )  E") : local_scope.

Notation "'\sum_' ( i : t | P ) E" :=
   (iprod plus 0 (fun i : t => P) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t | P ) E" :=
   (iprod mult 1 (fun i : t => P) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i ) E" := (iprod plus 0 (setA _) (fun i => E))
   (at level 40, E at level 40, i at level 50,
   format "'\sum_' ( i )  E") : local_scope.
Notation "'\prod_' ( i ) E" := (iprod mult 1 (setA _) (fun i => E))
   (at level 35, E at level 35, i at level 50 ,
   format "'\prod_' ( i )  E") : local_scope.

Notation "'\sum_' ( i : t ) E" := (iprod plus 0 (setA _) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t ) E" := (iprod mult 1 (setA _) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i < n ) E" := (iprod plus 0 (setA _) (fun i : I_(n) => E))
   (at level 40, E at level 40, i, n at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i < n ) E" := (iprod mult 1 (setA _) (fun i : I_(n) => E))
   (at level 35, E at level 35, i, n at level 50, only parsing) : local_scope.

(* Instantiating and (rationally) renaming, the "indexed product" lemmas. *)
(* This is a first batch -- there's a much larger set that depends on the *)
(* ring axioms down below.                                                *)

(* Extensionality (i.e., congruence); all variants. *)

Lemma eq_isum : forall (d : finType) (r r' : set d) F F',
  r =1 r' -> dfequal r F F' -> \sum_(in r) F = \sum_(in r') F'.
Proof. move=> d r r' F F'; move/(eq_iprod_set R) <-; exact: eq_iprod_f. Qed.

Lemma eq_iprod : forall (d : finType) (r r' : set d) F F',
  r =1 r' -> dfequal r F F' -> \prod_(in r) F = \prod_(in r') F'.
Proof. move=> d r r' F F'; move/(eq_iprod_set R) <-; exact: eq_iprod_f. Qed.

Lemma eq_isumL : forall (d : finType) (r r' : set d) F,
  r =1 r' -> \sum_(in r) F = \sum_(in r') F.
Proof. move=> *; exact: eq_isum. Qed.
Implicit Arguments eq_isumL [d F].

Lemma eq_isumR : forall (d : finType) (r : set d) F F',
   dfequal r F F' -> \sum_(in r) F = \sum_(in r) F'.
Proof. move=> *; exact: eq_isum. Qed.
Implicit Arguments eq_isumR [d r].

Lemma eq_iprodL : forall (d : finType) (r r' : set d) F,
  r =1 r' -> \prod_(in r) F = \prod_(in r') F.
Proof. move=> *; exact: eq_iprod. Qed.
Implicit Arguments eq_iprodL [d F].

Lemma eq_iprodR : forall (d : finType) (r : set d) F F',
   dfequal r F F' -> \prod_(in r) F = \prod_(in r) F'.
Proof. move=> *; exact: eq_iprod. Qed.
Implicit Arguments eq_iprodR [d r].

(* Renormalizing notations that the pretty-printer doesn't recognize. *)

Lemma isum_eta : forall (d : finType) r F,
  \sum_(in r) F = \sum_(i : d | r i) F i.
Proof. move=> *; exact: eq_isum. Qed.
 
Lemma isum_etaA : forall (d : finType) F, \sum_() F = \sum_(i : d) F i.
Proof. move=> *; exact: eq_isum. Qed.
 
Lemma iprod_eta : forall (d : finType) r F,
  \prod_(in r) F = \prod_(i : d | r i) F i.
Proof. move=> *; exact: eq_iprod. Qed.
 
Lemma iprod_etaA : forall (d : finType) F, \prod_() F = \prod_(i : d) F i.
Proof. move=> *; exact: eq_iprod. Qed.

(* Basic linear algebra (matrices). The matrix type is extensional, for   *)
(* now; it's packaged with a concrete type and reasonable factory syntax, *)
(* however, so if we do decide to go for rings with equality, we could    *)
(* have intensional matrices.                                             *)
(*   We use dependent types (ordinals) for the indices so that ranges are *)
(* mostly inferred automatically; we may have to reconsider this design   *)
(* if it proves too unwieldly for block decomposition theory.             *)

Record matrix (m n : nat) : Type := Matrix {
   matrix_entry :> I_(m) -> I_(n) -> R
}.

Notation "'M_' ( m , n )" := (matrix m n)
  (at level 9, m, n at level 50, format "'M_' ( m ,  n )") : local_scope.
Notation "'M_' ( n )" := (matrix n n)
  (at level 9, m, n at level 50, format "'M_' ( n )") : local_scope.

Notation "'\matrix_' ( i , j ) E" := (Matrix (fun i j => E))
  (at level 35, E at level 35, i, j at level 50,
   format "'\matrix_' ( i ,  j )  E") : local_scope.
Notation "'\matrix_' ( i < m , j < n ) E" := (@Matrix m n (fun i j => E))
  (at level 35, E at level 35, i, m, j, n at level 50,
   only parsing) : local_scope.
Notation "'\matrix_' ( i , j < n ) E" := (@Matrix _ n (fun i j => E))
  (at level 35, E at level 35, i, j, n at level 50,
   only parsing) : local_scope.
Notation "'\matrix_' ( i < m , j ) E" := (@Matrix m _ (fun i j => E))
  (at level 35, E at level 35, i, m, j at level 50,
   only parsing) : local_scope.

Definition matrix_plus m n (A B : M_(m, n)) := \matrix_(i, j) (A i j + B i j).

Definition matrix_scale m n x (A : M_(m, n)) := \matrix_(i, j) (x * A i j).

Definition matrix_mul m n p (A : M_(m, n)) (B : M_(n, p)) :=
  \matrix_(i, k) \sum_(j) A i j * B j k.

Definition matrix_transpose m n (A : M_(m, n)) := \matrix_(i, j) A j i.

Definition null_matrix m n := \matrix_(i < m, j < n) 0.

Definition perm_matrix n (s : S_(n)) :=
  \matrix_(i < n, j < n) (if s i == j then 1 else 0).

Definition unit_matrix n := \matrix_(i < n, j < n) (if i == j then 1 else 0).

CoInductive matrix_eq m n (A B : M_(m, n)) : Prop := EqMatrix of A =2 B.

Definition matrix_row m n i0 (A : M_(m, n)) := \matrix_(i < 1, j) A i0 j.

Definition matrix_col m n j0 (A : M_(m, n)) := \matrix_(i, j < 1) A i j0.

Definition matrix_rem_row m n i0 (A : M_(m, n)) :=
  \matrix_(i, j) A (lift i0 i) j.

Definition matrix_rem_col m n j0 (A : M_(m, n)) :=
  \matrix_(i, j) A i (lift j0 j).

(* The shape of the (dependent) height parameter determines where *)
(* the cut is made! *)

Definition matrix_lcut m1 m2 n (A : M_(m1 + m2, n)) :=
  \matrix_(i, j) A (lshift m2 i) j.

Definition matrix_rcut m1 m2 n (A : M_(m1 + m2, n)) :=
  \matrix_(i, j) A (rshift m1 i) j.

Definition matrix_paste m1 m2 n (A1 : M_(m1, n)) (A2 : M_(m2, n)) :=
   \matrix_(i, j) match split i with inl i1 => A1 i1 j | inr i2 => A2 i2 j end.

(* Operator syntax, basic style, for local use only. *)
(* Generic syntax would really help here...          *)

Notation "'\0m_' ( m , n )" := (null_matrix m n)
  (at level 0, format "'\0m_' ( m ,  n )") : local_scope.
Notation "'\0m_' ( n )" := (null_matrix n n)
  (at level 0, format "'\0m_' ( n )") : local_scope.
Notation "'\0m'" := (null_matrix _ _)
  (at level 0, format "'\0m'") : local_scope.
Notation "'\1m_' ( n )" := (unit_matrix n)
  (at level 0, format "'\1m_' ( n )") : local_scope.
Notation "'\1m'" := (unit_matrix _)
  (at level 0, format "'\1m'") : local_scope.
Notation "A '+m' B" := (matrix_plus A B) (at level 50) : local_scope.
Notation "A '+m' B" := (matrix_plus A B) (at level 50) : local_scope.
Notation "x '*sm' A" := (matrix_scale x A) (at level 40) : local_scope.
Notation "A '*m' B" := (matrix_mul A B) (at level 40) : local_scope.
Notation "'\^t' A" := (matrix_transpose A) (at level 10) : local_scope.
Notation "A '=m' B" := (matrix_eq A B) (at level 70) : local_scope.

Notation Local row := matrix_row.
Notation Local row' := matrix_rem_row.
Notation Local col := matrix_col.
Notation Local col' := matrix_rem_col.
Notation Local lcut := matrix_lcut.
Notation Local rcut := matrix_rcut.
Notation Local paste := matrix_paste.

(* The extensional setoid for matrices (crippled by setoid bugs) *)

Lemma matrix_eq_refl : forall m n, reflexive _ (@matrix_eq m n).
Proof. done. Qed.

Lemma matrix_eq_sym : forall m n, symmetric _ (@matrix_eq m n).
Proof. by move=> m n A B [AB]; split=> i j; rewrite AB. Qed.

Lemma matrix_eq_trans : forall m n, transitive _ (@matrix_eq m n).
Proof. by move=> m n A B c [AB] [BC]; split=> i j; rewrite AB BC. Qed.

Add Relation matrix matrix_eq
    reflexivity proved by matrix_eq_refl
    symmetry proved by matrix_eq_sym
    transitivity proved by matrix_eq_trans
  as matrix_extensionality.

(* Broken! Thus, we'll have to segregate matrix equational reasoning. Bummer...
Add Morphism matrix_entry with
  signature matrix_eq ==> eq ==> eq ==> eq
  as matrix_entry_extensional.
Proof. by move=> m n A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.
*)

Add Morphism matrix_plus with
  signature matrix_eq ==> matrix_eq ==> matrix_eq
  as matrix_plus_extensional.
Proof.
by move=> m n A1 A2 [A12] B1 B2 [B12]; split=> i j /=; rewrite A12 B12.
Qed.

Add Morphism matrix_scale with
  signature eq ==> matrix_eq ==> matrix_eq
  as matrix_scale_extensional.
Proof. by move=> m n x A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_mul with
  signature matrix_eq ==> matrix_eq ==> matrix_eq
  as matrix_mult_extensional.
Proof.
move=> m n p A1 A2 [A12] B1 B2 [B12].
by split=> i k; apply: eq_isumR => j _; rewrite A12 B12.
Qed.

Add Morphism matrix_transpose with
  signature matrix_eq ==> matrix_eq
  as matrix_transpose_extensional.
Proof. by move=> m n A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_row with
  signature eq ==> matrix_eq ==> matrix_eq
  as matrix_row_extensional.
Proof. by move=> m n i0 A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_rem_row with
  signature eq ==> matrix_eq ==> matrix_eq
  as matrix_rem_row_extensional.
Proof. by move=> m n i0 A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_col with
  signature eq ==> matrix_eq ==> matrix_eq
  as matrix_col_extensional.
Proof. by move=> m n j0 A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_rem_col with
  signature eq ==> matrix_eq ==> matrix_eq
  as matrix_rem_col_extensional.
Proof. by move=> m n j0 A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_lcut with
  signature matrix_eq ==> matrix_eq
  as matrix_lcut_extensional.
Proof. by move=> m n i0 A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_rcut with
  signature matrix_eq ==> matrix_eq
  as matrix_rcut_extensional.
Proof. by move=> m n i0 A1 A2 [A12]; split=> i j /=; rewrite A12. Qed.

Add Morphism matrix_paste with
  signature matrix_eq ==> matrix_eq ==> matrix_eq
  as matrix_paste_extensional.
Proof.
move=> m1 m2 n A1 A2 [A12] B1 B2 [B12]; split=> i j /=.
case: split => s; [exact: A12 | exact: B12].
Qed.

Lemma perm_matrix1 : forall n, perm_matrix 1%G =m \1m_(n).
Proof. by move=> n; split=> i j /=; rewrite perm1. Qed.
 
Lemma matrix_transposeK : forall m n (A : M_(m, n)), \^t (\^t A) =m A.
Proof. done. Qed.

Lemma matrix_transpose_inj : forall m n (A B : M_(m, n)),
  \^t A =m \^t B -> A =m B.
Proof.
by move=> m n A B tAB; rewrite -(matrix_transposeK A) tAB matrix_transposeK.
Qed.

Lemma matrix_transpose_perm : forall n (s : S_(n)),
  \^t (perm_matrix s) =m perm_matrix s^-1.
Proof.
by split=> i j /=; rewrite eq_sym -{1}(permKv s i) (inj_eq (@perm_inj _ s)).
Qed.

Lemma matrix_transpose_unit : forall n, \^t \1m_(n) =m \1m.
Proof. by split=> i j /=; rewrite eq_sym. Qed.

Lemma matrix_transpose_plus : forall m n (A B : M_(m, n)),
  \^t (A +m B) =m \^t A +m \^t B.
Proof. done. Qed.

Lemma matrix_transpose_scale : forall m n x (A : M_(m, n)),
  \^t (x *sm A) =m x *sm \^t A.
Proof. done. Qed.

Lemma matrix_transpose_row : forall m n i0 (A : M_(m, n)),
  \^t (row i0 A) = col i0 (\^t A).
Proof. done. Qed.

Lemma matrix_transpose_rem_row : forall m n i0 (A : M_(m, n)),
  \^t (row' i0 A) = col' i0 (\^t A).
Proof. done. Qed.

Lemma matrix_transpose_col : forall m n j0 (A : M_(m, n)),
  \^t (col j0 A) = row j0 (\^t A).
Proof. done. Qed.

Lemma matrix_transpose_rem_col : forall m n j0 (A : M_(m, n)),
  \^t (col' j0 A) = row' j0 (\^t A).
Proof. done. Qed.

Lemma matrix_eq_row : forall m n i0 (A : M_(m, n)) B,
  row i0 A =m B -> A i0 =1 B ord0.
Proof. by move=> m n i0 A B [AB] j; rewrite -AB. Qed.

Lemma matrix_eq_rem_row : forall m n i i0 (A B : M_(m, n)),
  i0 != i -> row' i0 A =m row' i0 B -> A i =1 B i.
Proof. move=> m n i i0 A B; case/unlift_some=> i' -> _  [AB] j; exact: AB. Qed.

Lemma matrix_paste_cut : forall m1 m2 n (A : matrix (m1 + m2) n),
  matrix_paste (matrix_lcut A) (matrix_rcut A) =m A.
Proof.
split=> i j /=; case: splitP => k Dk; congr matrix_entry; exact: val_inj.
Qed.

(* Determinants, in one line ! *)

Coercion odd_perm : permType >-> bool.

Definition determinant n (A : M_(n)) :=
  \sum_(s : S_(n)) (-1) ^ s * \prod_(i) A i (s i).

Notation "'\det' A" := (determinant A)
  (at level 10, A at level 9) : local_scope.

(*  Impossible : internal Coq assert failure !!!
Add Morphism determinant with
  signature matrix_eq ==> eq
  as determinant_extensional.
*)
Lemma determinant_extensional : forall n (A1 A2 : M_(n)),
  A1 =m A2 -> \det A1 = \det A2.
Proof.
move=> n A1 A2 [A12]; apply: eq_isumR => s _; congr (_ * _).
by apply: eq_iprodR => i _.
Qed.

(* The trace, just for fun ... *)

Definition matrix_trace (n : nat) (A : M_(n)) := \sum_(i) (A i i).

Notation "'\tr' A" := (matrix_trace A)
  (at level 10, A at level 9) : local_scope.

(*  Impossible : internal Coq assert failure !!!
Add Morphism matrix_trace with
  signature matrix_eq ==> eq
  as determinant_extensional.
*)
Lemma matrix_trace_extensional : forall n (A B : M_(n)),
  A =m B -> \tr A = \tr B.
Proof. by move=> n A B [A12]; apply: eq_isumR => i _. Qed.

Section R_props.

(* The ring axioms, and some useful basic corollaries. *)

Hypothesis mult1x : forall x, 1 * x = x.
Hypothesis mult0x : forall x : R, 0 * x = 0.
Hypothesis plus0x : forall x : R, 0 + x = x.
Hypothesis minusxx : forall x : R, x - x = 0.
Hypothesis plusA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x1 + x2 + x3.
Hypothesis plusC : forall x1 x2 : R, x1 + x2 = x2 + x1.
Hypothesis multA : forall x1 x2 x3 : R, x1 * (x2 * x3) = x1 * x2 * x3.
Hypothesis multC : forall x1 x2 : R, x1 * x2 = x2 * x1.
Hypothesis distrR : forall x1 x2 x3 : R, (x1 + x2) * x3 = x1 * x3 + x2 * x3.

Lemma plusCA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x2 + (x1 + x3).
Proof. move=> *; rewrite !plusA; congr (_ + _); exact: plusC. Qed.

Lemma multCA : forall x1 x2 x3 : R, x1 * (x2 * x3) = x2 * (x1 * x3).
Proof. move=> *; rewrite !multA; congr (_ * _); exact: multC. Qed.

Lemma distrL : forall x1 x2 x3 : R, x1 * (x2 + x3) = x1 * x2 + x1 * x3.
Proof. by move=> x1 x2 x3; rewrite !(multC x1) distrR. Qed.

Lemma oppK : involutive opp.
Proof.
by move=> x; rewrite -{2}[x]plus0x -(minusxx (- x)) plusC plusA minusxx plus0x.
Qed.

Lemma multm1x : forall x, -1 * x = -x.
Proof.
move=> x; rewrite -[_ * x]plus0x -(minusxx x) -{1}[x]mult1x plusC plusCA plusA.
by rewrite -distrR minusxx mult0x plus0x.
Qed.

Lemma mult_opp : forall x1 x2 : R, (- x1) * x2 = - (x1 * x2).
Proof. by move=> *; rewrite -multm1x -multA multm1x. Qed.

Lemma opp_plus : forall x1 x2 : R, - (x1 + x2) = - x1 - x2.
Proof.
by move=> x1 x2; rewrite -multm1x multC distrR -!(multC -1) !multm1x.
Qed.

Lemma RofSnE : forall n, RofSn n = n + 1.
Proof. by elim=> /= [|_ -> //]; rewrite plus0x. Qed.

Lemma Raddn : forall m n, (m + n)%N = m + n :> R.
Proof.
move=> m n; elim: m => /= [|m IHm]; first by rewrite plus0x.
by rewrite !RofSnE IHm plusC plusCA plusA.
Qed.

Lemma Rsubn : forall m n, m >= n -> (m - n)%N = m - n :> R.
Proof.
move=> m n; move/leq_add_sub=> Dm.
by rewrite -{2}Dm Raddn -plusA plusCA minusxx plusC plus0x.
Qed.

Lemma Rmuln : forall m n, (m * n)%N = m * n :> R.
Proof.
move=> m n; elim: m => /= [|m IHm]; first by rewrite mult0x.
by rewrite Raddn RofSnE IHm distrR mult1x plusC.
Qed.

Lemma RexpSnE : forall x n, RexpSn x n = x ^ n * x.
Proof. by move=> x; elim=> /= [|_ -> //]; rewrite mult1x. Qed.

Lemma mult_exp : forall x1 x2 n, (x1 * x2) ^ n = x1 ^ n * x2 ^ n.
Proof.
by move=> x1 x2; elim=> //= n IHn; rewrite !RexpSnE IHn -!multA (multCA x1).
Qed.

Lemma exp_addn : forall x n1 n2, x ^ (n1 + n2) = x ^ n1 * x ^ n2.
Proof.
move=> x n1 n2; elim: n1 => /= [|n1 IHn]; first by rewrite mult1x.
by rewrite !RexpSnE IHn multC multCA multA.
Qed.

Lemma Rexpn : forall m n, (m ^ n)%N = m ^ n :> R.
Proof. by move=> m; elim=> //= n IHn; rewrite Rmuln RexpSnE IHn multC. Qed.

Lemma exp0n : forall n, 0 < n -> 0 ^ n = 0.
Proof. by move=> [|[|n]] //= _; rewrite multC mult0x. Qed.

Lemma exp1n : forall n, 1 ^ n = 1.
Proof. by elim=> //= n IHn; rewrite RexpSnE IHn mult1x. Qed.

Lemma exp_muln : forall x n1 n2, x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
move=> x n1 n2; rewrite mulnC; elim: n2 => //= n2 IHn.
by rewrite !RexpSnE exp_addn IHn multC.
Qed.

Lemma sign_odd : forall n, (-1) ^ odd n = (-1) ^ n.
Proof.
move=> n; rewrite -{2}[n]odd_double_half addnC double_mul2 exp_addn exp_muln.
by rewrite /= multm1x oppK exp1n mult1x.
Qed.

Lemma sign_addb : forall b1 b2, (-1) ^ (b1 (+) b2) = (-1) ^ b1 * (-1) ^ b2.
Proof. by do 2!case; rewrite //= ?multm1x ?mult1x ?oppK. Qed.

Lemma sign_permM : forall d (s t : permType d),
  (-1) ^ (s * t)%G = (-1) ^ s * (-1) ^ t.
Proof. by move=> *; rewrite odd_permM sign_addb. Qed.

(* Instantiating and completing the set of lemmas lemmas for manipulating *)
(* indexed sums and products (for reindexing, splitting, and inverting).  *)

(* Domain-based equalities *)

Lemma isum_set0_eq : forall (d : finType) (F : d -> R), \sum_(in set0) F = 0.
Proof. move=> d F; exact: iprod0. Qed.

Lemma isum_set0 : forall (d : finType) (r : set d) F,
  r =1 set0 -> \sum_(in r) F = 0.
Proof. move=> d r F; move/eq_isumL->; exact: isum_set0_eq. Qed.

Lemma iprod_set0_eq : forall (d : finType) (F : d -> R), \prod_(in set0) F = 1.
Proof. move=> d F; exact: iprod0. Qed.

Lemma iprod_set0 : forall (d : finType) (r : set d) F,
  r =1 set0 -> \prod_(in r) F = 1.
Proof. move=> d r F; move/eq_iprodL->; exact: iprod_set0_eq. Qed.

Lemma isum_set1_eq : forall (d : finType) (i0 : d) F,
  \sum_(in set1 i0) F = F i0.
Proof. move=> d i0 F; exact: iprod_set1. Qed.

Lemma isum_set1 : forall (d : finType) i0 (r : set d) F,
  r =1 set1 i0 -> \sum_(in r) F = F i0.
Proof. move=> d i0 r F; move/eq_isumL->; exact: isum_set1_eq. Qed.
Implicit Arguments isum_set1 [d r F].

Lemma iprod_set1_eq : forall (d : finType) (i0 : d) F,
  \prod_(in set1 i0) F = F i0.
Proof. move=> d i0 F; exact: iprod_set1. Qed.

Lemma iprod_set1 : forall (d : finType) i (r : set d) F,
  r =1 set1 i -> \prod_(in r) F = F i.
Proof. move=> d i r F; move/eq_iprodL->; exact: iprod_set1_eq. Qed.
Implicit Arguments iprod_set1 [d r F].

Lemma isumD1 : forall (d : finType) i0 (r : set d) F,
  r i0 -> \sum_(in r) F = F i0 + \sum_(i | (i0 != i) && r i) F i.
Proof. move=> *; exact: iprodD1. Qed.
Implicit Arguments isumD1 [d r F].

Lemma iprodD1 : forall (d : finType) i0 (r : set d) F,
  r i0 -> \prod_(in r) F = F i0 * \prod_(i | (i0 != i) && r i) F i.
Proof. move=> *; exact: iprodD1. Qed.
Implicit Arguments iprodD1 [d r F].

(* The ID is easier to use than the setU one, because it avoids the messy *)
(* disjointness side condition.                                           *)

Lemma isumID : forall (d : finType) c r F,
  \sum_(in r) F = \sum_(i : d | r i && c i) F i + \sum_(i | r i && ~~ c i) F i.
Proof.
move=> d c r F; rewrite -iprod_setU /setU //.
 by apply: eq_isumL=> i; case r; case c.
by apply/set0P=> i; rewrite /setI; case r; case c.
Qed.

Lemma iprodID : forall (d : finType) c r F,
  \prod_(in r) F =
    \prod_(i : d | r i && c i) F i * \prod_(i | r i && ~~ c i) F i.
Proof.
move=> d c r F; rewrite -iprod_setU /setU //.
  by apply: eq_iprodL=> i; case r; case c.
by apply/set0P=> i; rewrite /setI; case r; case c.
Qed.

(* Arithmetic identities. The standard lemmas spin off side conditions when *)
(* subterm matching seems unlikely to succeed; we might consider removing   *)
(* the strict variants altogether.                                          *)

Lemma isum0_eq : forall (d : finType) (r : set d),
  \sum_(in r) (fun _ => 0) = 0.
Proof. move=> d r; exact: iprod_1. Qed.

Lemma isum0 : forall (d : finType) (r : set d) F,
  dfequal r F (fun _ => 0) -> \sum_(in r) F = 0.
Proof. move=> d r F; move/eq_isumR->; exact: isum0_eq. Qed.

Lemma iprod1_eq : forall (d : finType) (r : set d),
  \prod_(in r) (fun _ => 1) = 1.
Proof. move=> d r; exact: iprod_1. Qed.

Lemma iprod1 : forall (d : finType) (r : set d) F,
  dfequal r F (fun _ => 1) -> \prod_(in r) F = 1.
Proof. move=> d r F; move/eq_iprodR->; exact: iprod1_eq. Qed.

Lemma isum_plus : forall (d : finType) (r : set d) F1 F2,
  \sum_(i in r) (F1 i + F2 i) = \sum_(i in r) F1 i + \sum_(i in r) F2 i.
Proof. by move=> d r F1 F2; rewrite iprod_mul. Qed.

Lemma iprod_mult : forall (d : finType) (r : set d) F1 F2,
  \prod_(i in r) (F1 i * F2 i) = \prod_(i in r) F1 i * \prod_(i in r) F2 i.
Proof. by move=> d r F1 F2; rewrite iprod_mul. Qed.

Lemma isum_distrR : forall (d : finType) x (r : set d) F,
  (\sum_(in r) F) * x = \sum_(i in r) F i * x.
Proof. by move=> d x r F; rewrite isum_eta i_prod_distr. Qed.

Lemma isum_distrL : forall (d : finType) x (r : set d) F,
  x * (\sum_(in r) F) = \sum_(i in r) x * F i.
Proof.
by move=> *; rewrite multC isum_distrR; apply: eq_isumR => i _; rewrite multC.
Qed.

Lemma isum_opp : forall (d : finType) (r : set d) F,
  \sum_(i in r) - F i = - (\sum_(i in r) F i).
Proof.
move=> d r F; rewrite -multm1x isum_distrL.
by apply: eq_isum => // i _; rewrite multm1x.
Qed.

Lemma isum_id : forall (d : finType) (r : set d) x,
  \sum_(i in r) x = card r * x.
Proof.
move=> d r x; elim: {r}_`+1 {-2}r (ltnSn (card r)) => // n IHn r.
case: (pickP r) => [i ri | r0 _]; last by rewrite isum_set0 ?eq_card0.
rewrite (cardD1 i) (isumD1 i) ri //=; move/IHn=> -> {n IHn}; rewrite RofSnE.
by rewrite distrR mult1x plusC.
Qed.

Lemma iprod_id :  forall (d : finType) (r : set d) x,
  \prod_(i in r) x = x ^ card r.
Proof.
move=> d r x; elim: {r}_`+1 {-2}r (ltnSn (card r)) => // n IHn r.
case: (pickP r) => [i ri | r0 _]; last by rewrite iprod_set0 ?eq_card0.
rewrite (cardD1 i) (iprodD1 i) ri //=.
by move/IHn=> -> {n IHn}; rewrite RexpSnE multC.
Qed.

Lemma iprod_opp : forall (d : finType) (r : set d) F,
  \prod_(i in r) - F i = (-1) ^ card r * \prod_(i in r) F i.
Proof.
move=> d r F; rewrite -iprod_id -iprod_mult.
by apply: eq_iprodR=> i _; rewrite multm1x.
Qed.

(* The change of variable lemmas are the main sum manipulation tools.        *)
(* We provide two interfaces to this functionality. In both of these the     *)
(* user supplies a function h that maps the new indices to the old ones.     *)
(* The two lemmas have different requirements for that function h:           *)
(*  - In the "plain" case, h must map indices 1-to-1 AND onto the old range. *)
(*    This is expressed with the ibijective predicate, so that the           *)
(*    construction of the required partial inverse h' to h can be confined   *)
(*    to the paragraph in which this (unique) side condition is discharged.  *)
(*  - Tn the "onto" case, h only needs to map the new indices onto the old   *)
(*    range. The user must supply the partial (left) inverse directly to the *)
(*    reindexing rewrite rule, because it is used to thin the new range.     *)
(* The "onto" interface is slightly less modular because the partial inverse *)
(* is defined in the surrounding scope, and part of the bijectivity proof is *)
(* done later when the expression for the new index range is simplified.     *)
(* However these are often minor drawbackss; on the other hand the "onto"    *)
(* side condition is simpler, and it's often inconvenient to make h map      *)
(* 1-to-1 to the old range, and even impossible if the old range spans its   *)
(* entire type and the new index type is larger than the old index type.     *)

Lemma reindex_isum_onto : forall (d d' : finType) (h : d' -> d) h' r F,
    dcancel r h' h -> 
  \sum_(in r) F = \sum_(i | (h' (h i) == i) && r (h i)) F (h i).
Proof.
move=> d d' h h' r F h'K.
elim: {r}_`+1 {-3}r h'K (ltnSn (card r)) => //= n IHn r h'K.
case: (pickP r) => [i ri | r0 _]; last first.
  by rewrite !isum_set0 // => x; rewrite r0 andbF.
rewrite ltnS (cardD1 i) ri add1n; move/IHn {n IHn}.
rewrite /setD1 isum_eta => IH.
rewrite (isumD1 i ri) (isumD1 (h' i)) h'K ?set11 //; congr (_ + _).
rewrite {}IH => [|j]; [apply: eq_isumL => j | by case/andP; auto].
rewrite (andbCA (~~ _)); case: eqP => //= hK; congr (~~ _ && _).
by apply/eqP/eqP=> [-> | <-] //; rewrite h'K.
Qed.
Implicit Arguments reindex_isum_onto [d d' r F].

Lemma reindex_isum : forall (d d' : finType) (h : d' -> d) r F,
  ibijective r h -> \sum_(in r) F = \sum_(i | r (h i)) F (h i).
Proof.
move=> d d' h r F [h' hK h'K]; rewrite (reindex_isum_onto h h' h'K).
by apply: eq_isumL => i; case Hi: (r _); rewrite ?andbF ?hK ?set11.
Qed.
Implicit Arguments reindex_isum [d d' r F].

Lemma reindex_iprod_onto : forall (d d' : finType) (h : d' -> d) h' r F,
    dcancel r h' h -> 
  \prod_(in r) F = \prod_(i | (h' (h i) == i) && r (h i)) F (h i).
Proof.
move=> d d' h h' r F h'K.
elim: {r}_`+1 {-3}r h'K (ltnSn (card r)) => //= n IHn r h'K.
case: (pickP r) => [i ri | r0 _]; last first.
  by rewrite !iprod_set0 // => x; rewrite r0 andbF.
rewrite ltnS (cardD1 i) ri add1n; move/IHn {n IHn}.
rewrite /setD1 iprod_eta => IH.
rewrite (iprodD1 i ri) (iprodD1 (h' i)) h'K ?set11 //; congr (_ * _).
rewrite {}IH => [|j]; [apply: eq_iprodL => j | by case/andP; auto].
rewrite (andbCA (~~ _)); case: eqP => //= hK; congr (~~ _ && _).
by apply/eqP/eqP=> [-> | <-] //; rewrite h'K.
Qed.
Implicit Arguments reindex_iprod_onto [d d' r F].

Lemma reindex_iprod : forall (d d' : finType) (h : d' -> d) r F,
  ibijective r h -> \prod_(in r) F = \prod_(i | r (h i)) F (h i).
Proof.
move=> d d' h r F [h' hK h'K]; rewrite (reindex_iprod_onto h h' h'K).
by apply: eq_iprodL => i; case Hi: (r _); rewrite ?andbF ?hK ?set11.
Qed.
Implicit Arguments reindex_iprod [d d' r F].

(* Lemmas for double sums (no product variant for now).   *)
(* Double sums are created by providing a classifier, and *)
(* eliminated by reindexing over pairs.                   *)

Lemma partition_isum : forall (d d': finType) (pr : set d) p (r : set d') F,
  (forall j, r j -> pr (p j)) ->
  \sum_(in r) F = \sum_(i in pr) \sum_(j | r j && (p j == i)) F j.
Proof.
move=> d d' pr p r F prp.
rewrite (eq_isumL _ (fun j => r j && pr (p j))); last first.
  by move=> i /=; case ri: (r i); rewrite // prp.
rewrite isum_eta; elim: {pr}_`+1 {-2}pr {prp} (ltnSn (card pr)) => // n IHn pr.
case: (pickP pr) => [i0 pri0 | pr0 _]; last first.
  by rewrite !isum_set0 => //= i; rewrite pr0 andbF.
rewrite ltnS (cardD1 i0) pri0 (isumD1 i0) //; move/IHn=> {n IHn} <-.
rewrite (isumID (fun j => p j == i0));
  (congr (_ + _); apply: eq_isumL) => [j | i].
- by case: eqP => [-> | _]; rewrite ?pri0 ?andbF ?andbT.
by rewrite /setD1 eq_sym -!andbA; do !bool_congr.
Qed.
Implicit Arguments partition_isum [d d' r F].

(* We provide three variants: the general dependent case, a simpler *)
(* non-dependent case, and an even simpler rangeless case.          *)

Lemma pair_isum_dep : forall (d d': finType) r r' (F : d -> d' -> R),
  \sum_(i in r) \sum_(in r' i) F i
    = \sum_(u | r (fst u) && r' (fst u) (snd u)) F (fst u) (snd u).
Proof.
move=> d d' r r' F; set p1 := @fst d d'; set p2 := @snd d d'.
rewrite (partition_isum r p1) => [|j]; last by case/andP.
apply: eq_isumR => i ri.
rewrite (reindex_isum_onto (pair i) p2) => [|[i' j]] /=.
  by rewrite isum_eta; apply: eq_isumL => j; rewrite !set11 ri andbT.
by case/andP=> _; move/eqP->.
Qed.

Lemma pair_isum : forall (d d': finType) r r' (F : d -> d' -> R),
  \sum_(i in r) \sum_(in r') F i =
    \sum_(u | r (fst u) && r' (snd u)) F (fst u) (snd u).
Proof. move=> *; exact: pair_isum_dep. Qed.

Lemma pair_isumA : forall (d d': finType) (F : d -> d' -> R),
  \sum_(i) \sum_() F i = \sum_(u) F (fst u) (snd u).
Proof. move=> *; exact: pair_isum. Qed.

(* Sum-Sum summation interchange                                     *)

Lemma exchange_isum_dep :
  forall (d d' : finType) (r : set d) (r' : d -> set d') (xr : set d') F,
    (forall i j, r i -> r' i j -> xr j) ->
  \sum_(i in r) \sum_(in r' i) F i =
    \sum_(j in xr) \sum_(i | r i && r' i j) F i j.
Proof.
move=> d d' r r' xr F rxr; rewrite !pair_isum_dep.
pose p u := let: (i, j) := u in (j, i).
rewrite (reindex_isum_onto (p _ _) (p _ _)) => [|[//]].
apply: eq_isum => [] [j i] //=; symmetry; rewrite set11 andbC.
case: (@andP (r i)) => //=; case; exact: rxr.
Qed.
Implicit Arguments exchange_isum_dep [d d' r r' F].

Lemma exchange_isum : forall (d d': finType) r r' (F : d -> d' -> R),
  \sum_(i in r) \sum_(in r') F i = \sum_(j in r') \sum_(i in r) F i j.
Proof.
move=> d d' r r' F; rewrite (exchange_isum_dep r') //; apply: eq_isumR => i Hi.
by apply: eq_isumL => j; rewrite Hi andbT.
Qed.

(* Product-Sum summation interchange -- the (expanded) sum is indexed by     *)
(* fgraphs. We must guard against the case where both the fgraphType and the *)
(* product range are empty, as then the product is 1 and the sum is 0. We do *)
(* this by requiring a default value for the sum range type in the general   *)
(* case as this is required by the pfunspace construct anyway; we provide    *)
(* special variants for the case where the product range is full where this  *)
(* requirement can be waived. All told, ther are five variants: partial/full *)
(* range X dependent/non-dependent + the full product and sum range case,    *)
(* where the expanded sum is full. This last case is used below to prove the *)
(* product morphism lemma for determinants.                                  *)

(* Partial families -- should be in tuple.v *)

Definition family := fgraph_prod.
Definition familyP := fgraph_prodP.

Definition pfamily (d : finType) d' y0 (r : set d) (a' : d -> set d') :=
  family (fun i => if r i then a' i else set1 y0).

Lemma distr_iprod_isum_dep :
  forall (d d': finType) j0 (r : set d) (r' : d -> set d') F,
  \prod_(i in r) (\sum_(in r' i) F i) =
     \sum_(f in pfamily j0 r r') \prod_(i in r) F i (f i).
Proof.
move=> d d' j0 r r' F; pose df := fgraphType d d'.
elim: {r}_`+1 {-2}r (ltnSn (card r)) => // m IHm r.
case: (pickP r) => [i1 ri1 | r0 _]; last first.
  rewrite (isum_set1 (fgraph_of_fun (fun _ => j0))) ?iprod_set0 // => f.
  apply/familyP/eqP=> [Df|<-{f} i]; last by rewrite r0 g2f set11.
  by apply/fgraphP=> i; move/(_ i): Df; rewrite r0 g2f; move/eqP.
rewrite ltnS (cardD1 i1) ri1 (iprodD1 i1) /setD1 //; move/IHm=> {m IHm} IH.
rewrite isum_distrR (partition_isum (r' i1) (fun f : df => f i1)); last first.
  by move=> f; move/familyP; move/(_ i1); rewrite ri1.
apply: eq_isum => // j1 r'j1; rewrite {}IH isum_distrL.
pose seti1 j (f : df) := fgraph_of_fun (fun i => if i1 == i then j else f i).
symmetry; rewrite (reindex_isum_onto (seti1 j1) (seti1 j0))=> [|f]; last first.
  case/andP=> _; move/eqP=> fi1; apply/fgraphP=> i.
  by rewrite !g2f; case: eqP => // <-.
apply: eq_isum => [f | f _].
  rewrite g2f !set11 andbT; apply/andP/familyP=> [|r'f]; [case | split].
  - move/eqP=> fi1; move/familyP=> r'f j; move/(_ j): r'f; rewrite g2f.
    by case: eqP => //= <- _; rewrite -fi1 !g2f !set11.
  - apply/eqP; apply/fgraphP=> j; move/(_ j): r'f; rewrite !g2f.
    by case: eqP=> //= <-; move/eqP.
  apply/familyP=> j; move/(_ j): r'f; rewrite !g2f.
  by case: eqP=> //= <- _; rewrite ri1.
rewrite (iprodD1 i1) // g2f set11; congr (_ * _); apply: eq_iprodR => i.
by rewrite g2f; case: eqP.
Qed.

Lemma distr_iprod_isum : forall (d d' : finType) j0 r r' (F : d -> d' -> R),
  \prod_(i in r) (\sum_(in r') F i) =
     \sum_(f in pfunspace j0 r r') \prod_(i in r) F i (f i).
Proof. move=> *; exact: distr_iprod_isum_dep. Qed.

Lemma distr_iprodA_isum_dep : forall (d d': finType) (r' : d -> set d') F,
  \prod_(i) (\sum_(in r' i) F i) = \sum_(f in family r') \prod_(i) F i (f i).
Proof.
move=> d d' r' F; case: (pickP (setA d')) => [j0 _ | d'0].
  exact: (distr_iprod_isum_dep j0).
have d's0: (_ : set d') =1 set0 by move=> ? j; have:= d'0 j.
case: (pickP (setA d)) => [i0 _ | d0].
  rewrite (iprodD1 i0) // isum_set0 // mult0x isum_set0 // => f.
  by apply/familyP; move/(_ i0); rewrite d's0.
have f0: d -> d' by move=> i; have:= d0 i.
rewrite iprod_set0 // (isum_set1 (fgraph_of_fun f0)) ?iprod_set0 // => f.
apply/familyP/eqP=> _; last by move=> i; have:= d0 i.
by apply/fgraphP=> j; have:= d0 j.
Qed.

Lemma distr_iprodA_isum : forall (d d': finType) (r' : set d') F,
  \prod_(i : d) (\sum_(in r') F i) =
    \sum_(f in tfunspace r') \prod_(i) F i (f i).
Proof. move=> *; exact: distr_iprodA_isum_dep. Qed.

Lemma distr_iprodA_isumA : forall (d d': finType) F,
  \prod_(i) (\sum_() F i) = \sum_(f : fgraphType d d') \prod_(i) F i (f i).
Proof.
move=> *; rewrite distr_iprodA_isum; apply: eq_isumL => f; exact/tfunspaceP.
Qed.

(* The matrix graded algebra, extensional. *)

Lemma matrix_plus0x : forall m n (A : M_(m, n)), \0m +m A =m A.
Proof. by split=> i j /=; rewrite plus0x. Qed.

Lemma matrix_plusC : forall m n (A B : M_(m, n)), A +m B =m B +m A.
Proof. by split=> i j /=; rewrite plusC. Qed.

Lemma matrix_plusA : forall m n (A B C : M_(m, n)),
  A +m (B +m C) =m A +m B +m C.
Proof. by split=> i j /=; rewrite plusA. Qed.

Lemma matrix_scale_0 : forall m n (A : M_(m, n)), 0 *sm A =m \0m.
Proof. by split=> i j /=; rewrite mult0x. Qed.

Lemma matrix_scale_1 : forall m n (A : M_(m, n)), 1 *sm A =m A.
Proof. by split=> i j /=; rewrite mult1x. Qed.

Lemma matrix_scale_distrR : forall m n x1 x2 (A : M_(m, n)),
  (x1 + x2) *sm A =m x1 *sm A +m x2 *sm A.
Proof. by split=> i j /=; rewrite distrR. Qed.

Lemma matrix_scale_distrL : forall m n x (A B : M_(m, n)),
  x *sm (A +m B) =m x *sm A +m x *sm B.
Proof. by move=> m n x A B; split=> i j /=; rewrite !(multC x) distrR. Qed.

Lemma matrix_scaleA : forall m n p x (A : M_(m, n)) (B : M_(n, p)),
  x *sm (A *m B) =m (x *sm A) *m B.
Proof.
by split=> i k /=; rewrite isum_distrL; apply: eq_isumR => j _; rewrite multA.
Qed.

Lemma matrix_scaleC : forall m n p x (A : M_(m, n)) (B : M_(n, p)),
  A *m (x *sm B) =m (x *sm A) *m B.
Proof. by split=> i k /=; apply: eq_isumR => j _; rewrite multCA multA. Qed.

Lemma matrix_mult1x : forall m n (A : M_(m, n)), \1m *m A =m A.
Proof.
move=> m n A; split=> i j /=; rewrite (isumD1 i) // set11 mult1x plusC.
rewrite isum0 ?plus0x // => i'; rewrite andbT; move/negbET->; exact: mult0x.
Qed.

Lemma matrix_transpose_mul : forall m n p (A : M_(m, n)) (B : M_(n, p)),
   \^t (A *m B) =m \^t B *m \^t A.
Proof. split=> k i; apply: eq_isumR => j _; exact: multC. Qed.

Lemma matrix_multx1 : forall m n (A : M_(m, n)), A *m \1m =m A.
Proof.
move=> m n A; apply: matrix_transpose_inj.
by rewrite matrix_transpose_mul matrix_transpose_unit matrix_mult1x.
Qed.

Lemma matrix_distrR : forall m n p (A1 A2 : M_(m, n)) (B : M_(n, p)),
  (A1 +m A2) *m B =m A1 *m B +m A2 *m B.
Proof.
move=> m n p A1 A2 B; split=> i k /=; rewrite -isum_plus.
by apply: eq_isumR => j _; rewrite -distrR.
Qed.

Lemma matrix_distrL : forall m n p (A : M_(m, n)) (B1 B2 : M_(n, p)),
  A *m (B1 +m B2) =m A *m B1 +m A *m B2.
Proof.
move=> m n p A B1 B2; apply: matrix_transpose_inj.
rewrite matrix_transpose_plus !matrix_transpose_mul.
by rewrite -matrix_distrR -matrix_transpose_plus.
Qed.

Lemma matrix_multA : forall m n p q
   (A : M_(m, n)) (B : M_(n, p)) (C : M_(p, q)),
  A *m (B *m C) =m A *m B *m C.
Proof.
move=> m n p q A B C; split=> i l /=.
transitivity (\sum_(k) (\sum_(j) (A i j * B j k * C k l))).
  rewrite exchange_isum; apply: eq_isumR => j _; rewrite isum_distrL.
  by apply: eq_isumR => k _; rewrite multA.
by apply: eq_isumR => j _; rewrite isum_distrR.
Qed.

Lemma perm_matrixM : forall n (s t : S_(n)),
  perm_matrix (s * t)%G =m perm_matrix s *m perm_matrix t.
Proof.
move=> n; split=> i j /=; rewrite (isumD1 (s i)) // set11 mult1x -permM.
rewrite isum0 => [|j']; first by rewrite plusC plus0x.
by rewrite andbT; move/negbET->; rewrite mult0x.
Qed.
 
Lemma matrix_trace_plus : forall n (A B : M_(n)), \tr (A +m B) = \tr A + \tr B.
Proof. by move=> n A B; rewrite -isum_plus. Qed.

Lemma matrix_trace_scale : forall n x (A : M_(n)), \tr (x *sm A) = x * \tr A.
Proof. by move=> *; rewrite isum_distrL. Qed.

Lemma matrix_trace_transpose : forall n (A : M_(n)), \tr (\^t A) = \tr A.
Proof. done. Qed.

Lemma matrix_trace_multC : forall m n (A : M_(m, n)) (B : M_(n, m)),
  \tr (A *m B) = \tr (B *m A).
Proof.
move=> m n A B; rewrite /(\tr _) exchange_isum.
apply: eq_isumR => j _; apply: eq_isumR => i _; exact: multC.
Qed.

(* And now, finally, the title feature. *)

Lemma determinant_multilinear : forall n (A B C : M_(n)) i0 b c,
    row i0 A =m b *sm row i0 B +m c *sm row i0 C ->
    row' i0 B =m row' i0 A -> row' i0 C =m row' i0 A ->
  \det A = b * \det B + c * \det C.
Proof.
move=> n A B C i0 b c ABC.
move/matrix_eq_rem_row=> BA; move/matrix_eq_rem_row=> CA.
rewrite !isum_distrL -isum_plus; apply: eq_isumR => s _.
rewrite -!(multCA (_ ^ s)) -distrL; congr (_ * _).
rewrite !(@iprodD1 _ i0 (setA _)) // (matrix_eq_row ABC) distrR !multA.
by congr (_ * _ + _ * _); apply: eq_iprodR => i;
   rewrite andbT => ?; rewrite ?BA ?CA.
Qed.

Lemma alternate_determinant : forall n (A : M_(n)) i1 i2,
  i1 != i2 -> A i1 =1 A i2 -> \det A = 0.
Proof.
move=> n A i1 i2 Di12 A12; pose r := I_(n).
pose t := transp i1 i2; pose tr s := (t * s)%G.
have trK : involutive tr by move=> s; rewrite /tr mulgA transp2 mul1g.
have Etr: forall s, odd_perm (tr s) = even_perm s.
  by move=> s; rewrite odd_permM odd_transp Di12.
rewrite /(\det _) (isumID (@even_perm r)) /=; set S1 := \sum_(in _) _.
rewrite -{2}(minusxx S1); congr (_ + _); rewrite {}/S1 -isum_opp.
rewrite (reindex_isum tr); last by exists tr.
symmetry; apply: eq_isum => [s | s seven]; first by rewrite negbK Etr.
rewrite -multm1x multA Etr seven (negbET seven) multm1x; congr (_ * _).
rewrite (reindex_iprod t); last by exists (t : _ -> _) => i _; exact: transpK.
apply: eq_iprodR => i _; rewrite permM /t.
by case: transpP => // ->; rewrite A12.
Qed.

Lemma determinant_transpose : forall n (A : M_(n)), \det (\^t A) = \det A.
Proof.
move=> n A; pose r := I_(n); pose ip p : permType r := p^-1.
rewrite /(\det _) (reindex_isum ip) /=; last first.
  by exists ip => s _; rewrite /ip invgK.
apply: eq_isumR => s _; rewrite odd_permV /= (reindex_iprod s).
  by congr (_ * _); apply: eq_iprodR => i _; rewrite permK.
by exists (s^-1 : _ -> _) => i _; rewrite ?permK ?permKv.
Qed.

Lemma determinant_perm : forall n s, \det (@perm_matrix n s) = (-1) ^ s.
Proof.
move=> n s; rewrite /(\det _) (isumD1 s) //.
rewrite iprod1 => [|i _]; last by rewrite /= set11.
rewrite isum0 => [|t Dst]; first by rewrite plusC plus0x multC mult1x.
case: (pickP (fun i => s i != t i)) => [i ist | Est].
  by rewrite (iprodD1 i) // multCA /= (negbET ist) mult0x.
move: Dst; rewrite andbT; case/eqP.
by apply: eq_fun_of_perm => i; move/eqP: (Est i).
Qed.

Lemma determinant1 : forall n, \det (unit_matrix n) = 1.
Proof.
move=> n; have:= @determinant_perm n 1%G; rewrite odd_perm1 => /= <-.
apply: determinant_extensional; symmetry; exact: perm_matrix1.
Qed.

Lemma determinant_scale : forall n x (A : M_(n)),
  \det (x *sm A) = x ^ n * \det A.
Proof.
move=> n x A; rewrite isum_distrL; apply: eq_isumR => s _.
by rewrite multCA iprod_mult iprod_id card_ordinal.
Qed.

Lemma determinantM : forall n (A B : M_(n)), \det (A *m B) = \det A * \det B.
Proof.
move=> n A B; rewrite isum_distrR.
pose AB (f : F_(n)) (s : S_(n)) i := A i (f i) * B (f i) (s i).
transitivity (\sum_(f) \sum_(s : S_(n)) (-1) ^ s * \prod_(i) AB f s i).
  rewrite exchange_isum; apply: eq_isumR => s _.
  by rewrite -isum_distrL distr_iprodA_isumA.
rewrite (isumID (fun f => uniq (fval f))) plusC isum0 ?plus0x => /= [|f Uf].
  rewrite (reindex_isum (fun s => val (pval s))); last first.
    have s0 : S_(n) := 1%G; pose uf (f : F_(n)) := uniq (fval f).
    pose pf f := if insub uf f is Some s then Perm s else s0.
    exists pf => /= f Uf; rewrite /pf (insubT uf Uf) //; exact: eq_fun_of_perm.
  apply: eq_isum => [s|s _]; rewrite ?(valP (pval s)) // isum_distrL.
  rewrite (reindex_isum (mulg s)); last first.
    by exists (mulg s^-1) => t; rewrite ?mulKgv ?mulKg.
  apply: eq_isumR => t _; rewrite iprod_mult multA multCA multA multCA multA.
  rewrite -sign_permM; congr (_ * _); rewrite (reindex_iprod s^-1); last first.
    by exists (s : _ -> _) => i _; rewrite ?permK ?permKv.
  by apply: eq_iprodR => i _; rewrite permM permKv ?set11 // -{3}[i](permKv s).
transitivity (\det (\matrix_(i, j) B (f i) j) * \prod_(i) A i (f i)).
  rewrite multC isum_distrL; apply: eq_isumR=> s _.
  by rewrite multCA iprod_mult.
suffices [i1 [i2 Ef12 Di12]]: exists i1, exists2 i2, f i1 = f i2 & i1 != i2.
  by rewrite (alternate_determinant Di12) ?mult0x => //= j; rewrite Ef12.
pose ninj i1 i2 := (f i1 == f i2) && (i1 != i2).
case: (pickP (fun i1 => ~~ set0b (ninj i1))) => [i1| injf].
  by case/set0Pn=> i2; case/andP; move/eqP; exists i1; exists i2.
case/(perm_uniqP f): Uf => i1 i2; move/eqP=> Dfi12; apply/eqP.
by apply/idPn=> Di12; case/set0Pn: (injf i1); exists i2; apply/andP.
Qed.

(* And now, the Laplace formula. *)

Definition cofactor n (A : M_(n)) (i j : I_(n)) :=
   (-1) ^ (val i + val j) * \det (row' i (col' j A)).

(* Same bug as determinant
Add Morphism cofactor with
  signature matrix_eq ==> eq ==> eq ==> eq
  as cofactor_extensional. *)
Lemma cofactor_extensional : forall n (A1 A2 : M_(n)),
  A1 =m A2 -> cofactor A1 =2 cofactor A2.
Proof.
move=> n A1 A2 A12 i j; apply: (congr1 (mult _)).
by apply: determinant_extensional; rewrite A12.
Qed.

Lemma expand_cofactor : forall n (A : M_(n)) i j,
  cofactor A i j =
    \sum_(s : S_(n) | s i == j) (-1) ^ s * \prod_(k | i != k) A k (s k).
Proof.
move=> n.
pose lsf i (s : S_(n`-1)) j k :=
  if unlift i k is Some k' then lift j (s k') else j.
have lsfE: forall i s j, (lsf i s j i = j)
                       * (forall k, lsf i s j (lift i k) = lift j (s k)).
- by split=> *; rewrite /lsf ?unlift_none ?liftK.
have inj_lsf : injective (lsf _ _ _).
  move=> i s j; apply: can_inj (lsf j s^-1 i) _ => k.
  by case: (unliftP i k) => [k'|] ->; rewrite !lsfE ?permK.
pose ls := perm_of_inj (inj_lsf _ _ _).
have ls1 : forall i, ls i 1%G i = 1%G.
  move=> i; apply: eq_fun_of_perm => k.
  by case: (unliftP i k) => [k'|] ->; rewrite p2f lsfE !perm1.
have lsM : forall i s j t k, (ls i s j * ls j t k)%G = ls i (s * t)%G k.
  move=> i s j t k; apply: eq_fun_of_perm=> l; rewrite permM !p2f.
  by case: (unliftP i l) => [l'|] ->; rewrite !lsfE ?permM.
have sign_ls: forall s i j, (-1)^(ls i s j) = (-1) ^ s * (-1)^(val i + val j).
  pose nfp (s : S_(n`-1)) k := s k != k.
  move=> s i j; elim: {s}_`+1 {-2}s (ltnSn (card (nfp s))) => // m IHm s Hm.
  case: (pickP (nfp s)) Hm => [k Dsk | s1 _ {m IHm}].
    rewrite ltnS (cardD1 k) Dsk => Hm; pose t := transp k (s^-1 k).
    rewrite -(mulKg t s) transpV -(lsM _ _ i).
    rewrite 2!sign_permM -multA -{}IHm; last first.
      apply: {m} leq_trans Hm; apply: subset_leq_card; apply/subsetP=> k'.
      rewrite /nfp /setD1 permM /t.
      case: transpP=> [->|-> Ds|]; rewrite ?permKv; first by rewrite set11.
        by rewrite andbb; apply/eqP=> Dk; case/eqP: Ds; rewrite {1}Dk permKv.
      by move/eqP; rewrite eq_sym => ->.
    suffices ->: ls i t i = transp (lift i k) (lift i (s^-1 k)).
      by rewrite !odd_transp (inj_eq (@lift_inj _ _)).
    apply: eq_fun_of_perm=> i'; rewrite p2f.
    case: (unliftP i i') => [i''|] ->; rewrite lsfE.
      rewrite inj_transp //; exact: lift_inj.
    case transpP => //; move/eqP; case/idPn; exact: neq_lift.
  have ->: s = 1%G.
    by apply: eq_fun_of_perm=> k; rewrite perm1; move/eqP: (s1 k).
  rewrite odd_perm1 mult1x; without loss: i {s s1} j / val j <= val i.
    case: (leqP (val j) (val i)); first by auto.
    move/ltnW=> ij; move/(_ _ _ ij)=> Wji.
    rewrite -(mulgK (ls j 1%G i) (ls i  _ j)) lsM !(ls1,mul1g).
    by rewrite odd_permV addnC.
  move Dm: (val i)`+1 => m; elim: m i Dm => // m IHm i [im].
  rewrite leq_eqVlt; case/setU1P=> [eqji|ltji].
    by rewrite (val_inj eqji) ls1 odd_perm1 /= -sign_odd odd_addn addbb.
  have m'm: m`-1`+1 = m by rewrite -im (ltnSpred ltji).
  have ltm'n : m`-1 < n by rewrite m'm -im leq_eqVlt orbC (valP i).
  pose i' := make_ord ltm'n; rewrite -{1}(mulg1 1%G) -(lsM _ _ i') sign_permM.
  rewrite multC {}IHm; try by rewrite /= -1?ltnS ?m'm // -im.
  rewrite im -m'm addSn -addn1 (exp_addn _ _ 1); congr (_ * _).
  have{j ltji} ii' : i != i' by rewrite -val_eqE im /= -m'm eqn_leq ltnn.
  transitivity ((-1) ^ transp i i'); last by rewrite odd_transp ii'.
  congr (_ ^ odd_perm _); apply: eq_fun_of_perm=> k.
  case: (unliftP i k) => [k'|] -> {k}; rewrite p2f lsfE ?transpL // perm1.
  apply: val_inj; rewrite p2f /transpose (negbET (neq_lift _ _)) -val_eqE.
  rewrite fun_if /= im /bump; case mk': (m <= _).
    by rewrite eq_sym eqn_leq ltnNge leq_eqVlt m'm mk' orbT.
  by rewrite add0n leq_eqVlt m'm mk'; case: eqP => //= <-.
move=> A i0 j0; rewrite (reindex_isum (fun s => ls i0 s j0)); last first.
  pose ulsf i (s : S_(n)) k' :=
    if unlift (s i) (s (lift i k')) is Some k then k else k'.
  have ulsfE: forall i (s : S_(n)) k',
      lift (s i) (ulsf i s k') = s (lift i k').
    rewrite /ulsf => i s k'; have:= neq_lift i k'.
    by rewrite -(inj_eq (@perm_inj _ s)); case/unlift_some=> ? ? ->.
  have inj_ulsf: injective (ulsf i0 _).
    move=> s; apply: can_inj (ulsf (s i0) s^-1) _ => k'.
    by rewrite {1}/ulsf ulsfE !permK liftK.
  exists (fun s => perm_of_inj (inj_ulsf s)) => [s _ | s]. 
    by apply: eq_fun_of_perm=> k'; rewrite p2f /ulsf !p2f !lsfE liftK.
  move/eqP=> si0; apply: eq_fun_of_perm=> k.
  by case: (unliftP i0 k) => [k'|] ->; rewrite p2f lsfE // p2f -si0 ulsfE. 
rewrite /cofactor isum_distrL.
apply: eq_isum => [s | s _]; first by rewrite p2f lsfE set11.
rewrite multCA multA -{}sign_ls; congr (_ * _).
case: (pickP (setA I_(n`-1))) => [k'0 _ | r'0]; last first.
  rewrite !iprod_set0 // => k; apply/idP; case/unlift_some=> k'.
  by have:= r'0 k'.
rewrite (reindex_iprod (lift i0)).
  by apply: eq_iprod => [k | k _ /=]; [rewrite neq_lift | rewrite p2f lsfE].
pose f k := if unlift i0 k is Some k' then k' else k'0.
by exists f; rewrite /f => k; [rewrite liftK | case/unlift_some=> ? ? ->].
Qed.

Lemma expand_determinant_row : forall n (A : M_(n)) i0,
  \det A = \sum_(j) A i0 j * cofactor A i0 j.
Proof.
move=> n A i0; rewrite /(\det A).
rewrite (partition_isum (setA _) (fun s : S_(_) => s i0)) //.
apply: eq_isumR => j0 _; rewrite expand_cofactor isum_distrL.
apply: eq_isumR => s /=; move/eqP=> Dsi0.
by rewrite multCA (iprodID (set1 i0)) /= iprod_set1_eq Dsi0.
Qed.

Lemma cofactor_transpose : forall n (A : M_(n)) i j,
  cofactor (\^t A) i j = cofactor A j i.
Proof. by move=> n A i j; rewrite /cofactor addnC -determinant_transpose. Qed.

Lemma expand_determinant_col : forall n (A : M_(n)) j0,
  \det A = \sum_(i) (A i j0 * cofactor A i j0).
Proof.
move=> n A j0; rewrite -determinant_transpose (expand_determinant_row _ j0).
by apply: eq_isumR => i _; rewrite cofactor_transpose.
Qed.

(* The final flurry: adjugates. *)

Definition adjugate n (A : M_(n)) := \matrix_(i, j) (cofactor A j i).

Add Morphism adjugate with
  signature matrix_eq ==> matrix_eq
  as adjugate_extensional.
Proof.
by move=> n A1 A2 A12; split=> i j /=; rewrite (cofactor_extensional A12).
Qed.

Lemma mult_adugateR : forall n (A : M_(n)), A *m adjugate A =m \det A *sm \1m.
Proof.
move=> n A; split=> i1 i2 /=; rewrite multC.
case Di: (i1 == i2); first by rewrite (eqP Di) -expand_determinant_row mult1x.
pose B := \matrix_(i, j) (if i == i2 then A i1 j else A i j).
have EBi12: B i1 =1 B i2 by move=> j; rewrite /= set11 if_same.
rewrite mult0x -{2}(alternate_determinant (negbT Di) EBi12).
rewrite (expand_determinant_row _ i2) /= set11.
apply: eq_isumR => j _; do 2!apply: (congr1 (mult _)); apply: eq_isumR => s _.
by congr (_ * _); apply: eq_iprodR => i _ /=; rewrite eq_sym -if_neg neq_lift.
Qed.

Lemma transpose_adjugate : forall n (A : M_(n)),
  \^t (adjugate A) =m adjugate (\^t A).
Proof. split=> i j; symmetry; exact: cofactor_transpose. Qed.

Lemma mult_adugateL : forall n (A : M_(n)), adjugate A *m A =m  \det A *sm \1m.
Proof.
move=> n A; apply: matrix_transpose_inj.
rewrite matrix_transpose_mul transpose_adjugate mult_adugateR.
by rewrite  determinant_transpose matrix_transpose_scale matrix_transpose_unit.
Qed.

End R_props.

End determinant_context.
