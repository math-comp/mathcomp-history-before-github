(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(***************************************************************************)
(* The seq type is the ssreflect type for sequences; it is identical to    *)
(* the standard Coq list type, but supports a larger set of operations, as *)
(* well as eqType and predType structures. The operations are geared       *)
(* towards reflection, e.g., they generally expect and provide boolean     *)
(* predicates, and our membership predicates expects an eqType. To avoid   *)
(* any confusion we do not Import the Coq List module, which forces us to  *)
(* define our own Type since list is not defined in the pervasives.        *)
(*   Since there is no true subtyping in Coq, we don't use a type for non  *)
(* empty sequences; rather, we pass explicitly the head and "tail" of the  *)
(* sequence.                                                               *)
(*   The empty sequence is especially bothersome for subscripting, since   *)
(* it forces us to have a default value. We use a combination of syntactic *)
(* extensions/prettyprinting to hide it in most of the development.        *)
(*   Here is the list of seq operations :                                  *)
(*   - constructors : Nil, Cons (nil, cons if polymorphic), rcons          *)
(*   - factories : ncons, nseq (repeat sequence), seqn (n-ary).            *)
(*   - items from indexes : iota (index generation), mkseq.                *)
(*   - sequential access: ohead (option), head (w. default), behead,       *)
(*                        last, belast (non empty seqs)                    *)
(*   - random access: nth & set_nth (w. default), incr_nth (for seq nat)   *)
(*   - size: size (seq version of length), shape (= map size)              *)
(*   - elements lookup: index, mem_seq (implements the predType interface) *)
(*   - set operations: find, count, has, all, constant                     *)
(*   - filtering : filter, subfilter (to subType), sieve (bitseq masking)  *)
(*   - "no duplicates" predicate & function: uniq, undup                   *)
(*   - permutation equivalence: perm_eq, perm_eql & r (left & right trans) *)
(*   - surgery: cat, drop, take, rot, rotr, rev                            *)
(*   - iterators: map, pmap (partial funs), foldr (fold_right), foldl,     *)
(*                sumn, scanl, pairmap zip, unzip1 & 2, flatten, reshape   *)
(* The sieve operator uses a boolean sequence to select a subsequence; it  *)
(* is used heavily for the correctness of the config compilation.          *)
(* We are quite systematic in providing lemmas to rewrite any composition  *)
(* of two operations. "rev", whose simplifications are not natural, is     *)
(* protected with nosimpl.                                                 *)
(*  Notations:                                                             *)
(*    [::], x :: s, s1 ++ s2   nil, cons x s, cat s1 s2                    *)
(*    [:: x0; ... xn]          explicit seq                                *)
(*    [:: x0, ... xn & s]      multiple cons                               *)
(*    s`_i                     nth x0 s i for the appropriate x0           *)
(*                             (to be defined in the appropriate scope)    *)
(***************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

Inductive seq (T : Type) : Type := Nil | Cons of T & seq T.
Implicit Arguments Cons [].
Notation nil := (Nil _) (only parsing).
Notation cons := (Cons _).

Bind Scope seq_scope with seq.
Arguments Scope Cons [type_scope _ seq_scope].

Notation "x :: s" := (Cons _ x s)
  (at level 60, right associativity, format "x  ::  s") : seq_scope.

Reserved Notation "s1 ++ s2"
  (at level 60, right associativity, format "s1  ++  s2").

Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::])
  (at level 0, format "[ ::  x1 ]") : seq_scope.

Notation "[ :: x & s ]" := (x :: s) (only parsing) : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (x1 :: x2 :: .. (xn :: s) ..)
  (at level 0, format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : seq_scope.

Section Sequences.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type s : (seq T).

Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.

Lemma size0nil : forall s, size s = 0 -> s = [::]. Proof. by case. Qed.

Definition ohead s := if s is x :: _ then Some x else None.
Definition head s := if s is x :: _ then x else x0.

Definition behead s := if s is _ :: s' then s' else [::].

Lemma size_behead : forall s, size (behead s) = (size s).-1.
Proof. by case. Qed.

(* Factories *)

Definition ncons n x := iter n (cons x).
Definition nseq n x := ncons n x [::].

Lemma size_ncons : forall n x s, size (ncons n x s) = n + size s.
Proof. by move=> n x p; elim: n => //= n ->. Qed.

Lemma size_nseq : forall n x, size (nseq n x) = n.
Proof. by move=> *; rewrite size_ncons addn0. Qed.

(* n-ary, dependently typed constructor. *)

Fixpoint seqn_type n := if n is n'.+1 then T -> seqn_type n' else seq T.

Fixpoint seqn_rec f n {struct n} : seqn_type n :=
  if n is n'.+1 return seqn_type n then
    fun x => seqn_rec (fun s => f (x :: s)) n'
  else f [::].
Definition seqn := seqn_rec id.

(* Sequence catenation "cat".                                               *)

Fixpoint cat s1 s2 {struct s1} := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

Lemma cat0s : forall s, [::] ++ s = s. Proof. by []. Qed.

Lemma cat1s : forall x s, [:: x] ++ s = x :: s. Proof. by []. Qed.

Lemma cat_cons : forall x s1 s2, (x :: s1) ++ s2 = x :: s1 ++ s2.
Proof. by []. Qed.

Lemma cat_nseq : forall n x s, nseq n x ++ s = ncons n x s.
Proof. by move=> n x s; elim: n => //= n ->. Qed.

Lemma cats0 : forall s, s ++ [::] = s.
Proof. by elim=> //= x s ->. Qed.

Lemma catA : forall s1 s2 s3, s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof. by move=> s1 s2 s3; elim: s1 => //= x s1 ->. Qed.

Lemma size_cat : forall s1 s2, size (s1 ++ s2) = size s1 + size s2.
Proof. by move=> s1 s2; elim: s1 => //= x s1 ->. Qed.

(* last, belast, rcons, and last induction. *)

Fixpoint rcons s z {struct s} :=
  if s is x :: s' then x :: rcons s' z else [:: z].

Lemma rcons_cons : forall x s z, rcons (x :: s) z = x :: rcons s z.
Proof. by []. Qed.

Lemma cats1 : forall s z, s ++ [:: z] = rcons s z.
Proof. by move=> s z; elim: s => //= x s ->. Qed.

Fixpoint last x s {struct s} := if s is x' :: s' then last x' s' else x.

Fixpoint belast x s {struct s} :=
  if s is x' :: s' then x :: (belast x' s') else [::].

Lemma lastI : forall x s, x :: s = rcons (belast x s) (last x s).
Proof. by move=> x s; elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma last_cons : forall x y s, last x (y :: s) = last y s.
Proof. by []. Qed.

Lemma size_rcons : forall s x, size (rcons s x) = (size s).+1.
Proof. by move=> *; rewrite -cats1 size_cat addnC. Qed.

Lemma size_belast : forall x s, size (belast x s) = size s.
Proof. by move=> x s; elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma last_cat : forall x s1 s2, last x (s1 ++ s2) = last (last x s1) s2.
Proof. by move=> x s1 s2; elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.

Lemma last_rcons : forall x s z, last x (rcons s z) = z.
Proof. by move=> x s z; rewrite -cats1 last_cat. Qed.

Lemma belast_cat : forall x s1 s2,
  belast x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2.
Proof. by move=> x s1 s2; elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.

Lemma belast_rcons : forall x s z, belast x (rcons s z) = x :: s.
Proof. by move=> *; rewrite lastI -!cats1 belast_cat. Qed.

Lemma cat_rcons : forall x s1 s2, rcons s1 x ++ s2 = s1 ++ x :: s2.
Proof. by move=> *; rewrite -cats1 -catA. Qed.

Lemma rcons_cat : forall x s1 s2,
  rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
Proof. by move=> *; rewrite -!cats1 catA. Qed.

CoInductive last_spec : seq T -> Type :=
  | LastNil        : last_spec [::]
  | LastRcons s x  : last_spec (rcons s x).

Lemma lastP : forall s, last_spec s.
Proof. move=> [|x s]; [ left | rewrite lastI; right ]. Qed.

Lemma last_ind : forall P,
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof.
move=> P Hnil Hlast s; rewrite -(cat0s s).
elim: s [::] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
by rewrite -cat_rcons; auto.
Qed.

(* Sequence indexing. *)

Fixpoint nth s n {struct n} :=
  if s is x :: s' then if n is n'.+1 then @nth s' n' else x else x0.

Fixpoint set_nth s n y {struct n} :=
  if s is x :: s' then
    if n is n'.+1 then x :: @set_nth s' n' y else y :: s'
  else ncons n x0 [:: y].

Lemma nth0 : forall s, nth s 0 = head s. Proof. by []. Qed.

Lemma nth_default : forall s n, size s <= n -> nth s n = x0.
Proof. by elim=> [|x s IHs] [|n]; try exact (IHs n). Qed.

Lemma nth_nil : forall n, nth [::] n = x0.
Proof. by case. Qed.

Lemma last_nth : forall x s, last x s = nth (x :: s) (size s).
Proof. by move=> x s; elim: s x => [|y s IHs] x /=. Qed.

Lemma nth_last : forall s, nth s (size s).-1 = last x0 s.
Proof. by case=> //= x s; rewrite last_nth. Qed.

Lemma nth_behead : forall s n, nth (behead s) n = nth s n.+1.
Proof. by move=> [|x s] [|n]. Qed.

Lemma nth_cat : forall s1 s2 n,
 nth (s1 ++ s2) n = if n < size s1 then nth s1 n else nth s2 (n - size s1).
Proof.
by move=> s1 s2 n; elim: s1 n => [|x s1 IHs] [|n]; try exact (IHs n).
Qed.

Lemma nth_rcons : forall s x n,
  nth (rcons s x) n =
    (if n < size s then nth s n else if n == size s then x else x0).
Proof. by elim=> [|x s IHs] y [|n] //=; rewrite ?nth_nil ?IHs. Qed.

Lemma nth_ncons : forall m x s n,
  nth (ncons m x s) n = (if n < m then x else nth s (n - m)).
Proof. move=> m x s; elim: m => [|m IHm] [|n] //=; exact: IHm. Qed.

Lemma nth_nseq : forall m x n, nth (nseq m x) n = (if n < m then x else x0).
Proof. move=> m x; elim: m => [|m IHm] [|n] //=; exact: IHm. Qed.

Lemma eq_from_nth : forall s1 s2, size s1 = size s2 ->
  (forall i, i < size s1 -> nth s1 i = nth s2 i) -> s1 = s2.
Proof.
elim=> [|x1 s1 IHs1] [|x2 s2] //= [eq_sz] eq_s12.
rewrite [x1](eq_s12 0) // (IHs1 s2) // => i; exact: (eq_s12 i.+1).
Qed.

Lemma size_set_nth : forall s n y, size (set_nth s n y) = maxn n.+1 (size s).
Proof.
elim=> [|x s IHs] [|n] y //=.
- by rewrite size_ncons addn1 maxn0.
- by rewrite -add_sub_maxn subn1.
by rewrite IHs -add1n addn_maxr.
Qed.

Lemma set_nth_nil : forall n y, set_nth [::] n y = ncons n x0 [:: y].
Proof. by case. Qed.

Lemma nth_set_nth : forall s n y,
  nth (set_nth s n y) =1 [eta nth s with n |-> y].
Proof.
elim=> [|x s IHs] [|n] y [|m] //=; rewrite ?nth_nil ?IHs // nth_ncons eqSS.
case: ltngtP => // [lt_nm | ->]; last by rewrite subnn.
by rewrite nth_default // subn_gt0.
Qed.

Lemma set_set_nth : forall s n1 y1 n2 y2,
  set_nth (set_nth s n1 y1) n2 y2 =
   let s2 := set_nth s n2 y2 in if n1 == n2 then s2 else set_nth s2 n1 y1.
Proof.
move=> s n1 y1 n2 y2; case: eqP => [->|]; last move/eqP=> ne_n12.
  apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnA maxnn.
  by do 2!rewrite !nth_set_nth /=; case: eqP.
apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnCA.
do 2!rewrite !nth_set_nth /=; case: eqP => // ->.
by rewrite eq_sym -if_neg ne_n12.
Qed.

(* find, count, has, all. *)

Section SeqFind.

Variable a : pred T.

Fixpoint find s := if s is x :: s' then if a x then 0 else (find s').+1 else 0.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

Fixpoint has s := if s is x :: s' then a x || has s' else false.

Fixpoint all s := if s is x :: s' then a x && all s' else true.

Lemma count_filter : forall s, count s = size (filter s).
Proof. by elim=> [|x s IHs] //=; rewrite IHs; case (a x). Qed.

Lemma has_count : forall s, has s = (0 < count s).
Proof. by elim=> [|x s IHs] //=; rewrite IHs; case (a x). Qed.

Lemma count_size : forall s, count s <= size s.
Proof. by elim=> [|x s IHs] //=; case (a x); last by apply ltnW. Qed.

Lemma all_count : forall s, all s = (count s == size s).
Proof.
elim=> [|x s IHs] //=; case: (a x) => [|] //=.
by rewrite add0n eqn_leq andbC ltnNge count_size.
Qed.

Lemma all_filterP : forall s, reflect (filter s = s) (all s).
Proof.
move=> s; apply introP.
  by elim: s => [|x s IHs] //=; case/andP=> [Ha Hs]; rewrite Ha IHs.
rewrite all_count count_filter => neq_sz eq_f_s.
by rewrite eq_f_s eqxx in neq_sz.
Qed.

Lemma has_find : forall s, has s = (find s < size s).
Proof. by elim=> [|x s IHs] //=; case (a x); rewrite ?leqnn. Qed.

Lemma find_size : forall s, find s <= size s.
Proof. by elim=> [|x s IHs] //=; case (a x). Qed.

Lemma find_cat : forall s1 s2,
  find (s1 ++ s2) = if has s1 then find s1 else size s1 + find s2.
Proof.
move=> s1 s2; elim: s1 => [|x s1 IHs] //=; case: (a x) => [|] //.
by rewrite IHs (fun_if succn).
Qed.

Lemma has_nil : has [::] = false. Proof. by []. Qed.

Lemma has_seq1 : forall x, has [:: x] = a x.
Proof. by move=> *; rewrite /= orbF. Qed.

Lemma has_seqb : forall (b : bool) x, has (nseq b x) = b && a x.
Proof. by case=> // *; rewrite /= orbF. Qed.

Lemma all_nil : all [::] = true. Proof. by []. Qed.

Lemma all_seq1 : forall x, all [:: x] = a x.
Proof. by move=> *; rewrite /= andbT. Qed.

Lemma nth_find : forall s, has s -> a (nth s (find s)).
Proof. by elim=> [|x s IHs] //=; case Hx: (a x). Qed.

Lemma before_find : forall s i, i < find s -> a (nth s i) = false.
Proof.
move=> s i; elim: s i => [|x s IHs] //=; case Hx: (a x) => [|] // [|i] //.
exact (IHs i).
Qed.

Lemma filter_cat : forall s1 s2, filter (s1 ++ s2) = filter s1 ++ filter s2.
Proof.
by move=> s1 s2; elim: s1 => [|x s1 IHs] //=; rewrite IHs; case (a x).
Qed.

Lemma filter_rcons : forall s x,
  filter (rcons s x) = if a x then rcons (filter s) x else filter s.
Proof.
by move=> s x; rewrite -!cats1 filter_cat /=; case (a x); rewrite /= ?cats0.
Qed.

Lemma count_cat : forall s1 s2, count (s1 ++ s2) = count s1 + count s2.
Proof. by move=> *; rewrite !count_filter filter_cat size_cat. Qed.

Lemma has_cat : forall s1 s2, has (s1 ++ s2) = has s1 || has s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 IHs] //=; rewrite IHs orbA. Qed.

Lemma has_rcons : forall s x, has (rcons s x) = a x || has s.
Proof. by move=> *; rewrite -cats1 has_cat has_seq1 orbC. Qed.

Lemma all_cat : forall s1 s2, all (s1 ++ s2) = all s1 && all s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 IHs] //=; rewrite IHs andbA. Qed.

Lemma all_rcons : forall s x, all (rcons s x) = a x && all s.
Proof. by move=> *; rewrite -cats1 all_cat all_seq1 andbC. Qed.

End SeqFind.

Lemma eq_find : forall a1 a2, a1 =1 a2 -> find a1 =1 find a2.
Proof. by move=> a1 a2 Ea; elim=> [|x s IHs] //=; rewrite Ea IHs. Qed.

Lemma eq_filter : forall a1 a2, a1 =1 a2 -> filter a1 =1 filter a2.
Proof. by move=> a1 a2 Ea; elim=> [|x s IHs] //=; rewrite Ea IHs. Qed.

Lemma eq_count : forall a1 a2, a1 =1 a2 -> count a1 =1 count a2.
Proof. by move=> a1 a2 Ea s; rewrite !count_filter (eq_filter Ea). Qed.

Lemma eq_has : forall a1 a2, a1 =1 a2 -> has a1 =1 has a2.
Proof. by move=> a1 a2 Ea s; rewrite !has_count (eq_count Ea). Qed.

Lemma eq_all : forall a1 a2, a1 =1 a2 -> all a1 =1 all a2.
Proof. by move=> a1 a2 Ea s; rewrite !all_count (eq_count Ea). Qed.

Lemma filter_pred0 : forall s, filter pred0 s = [::]. Proof. by elim. Qed.

Lemma filter_predT : forall s, filter predT s = s.
Proof. by elim=> //= x s ->. Qed.

Lemma filter_predI : forall a1 a2 s,
  filter (predI a1 a2) s = filter a1 (filter a2 s).
Proof.
move=> a1 a2; elim=> [|x s IHs] //=; rewrite /= andbC IHs.
by case: (a2 x) => [|] //=; case (a1 x).
Qed.

Lemma count_pred0 : forall s, count pred0 s = 0.
Proof. by move=> s; rewrite count_filter filter_pred0. Qed.

Lemma count_predT : forall s, count predT s = size s.
Proof. by move=> s; rewrite count_filter filter_predT. Qed.

Lemma count_predUI : forall a1 a2 s,
 count (predU a1 a2) s + count (predI a1 a2) s = count a1 s + count a2 s.
Proof.
move=> a1 a2; elim=> [|x s IHs] //=; rewrite /= addnCA -addnA IHs addnA addnC.
by rewrite -!addnA; do 2 nat_congr; case (a1 x); case (a2 x).
Qed.

Lemma count_predC : forall a s, count a s + count (predC a) s = size s.
Proof.
move=> a; elim=> [|x s IHs] //=; rewrite -!addnA (addnCA (count a s)) IHs /=.
by case (a x).
Qed.

Lemma has_pred0 : forall s, has pred0 s = false.
Proof. by move=> s; rewrite has_count count_pred0. Qed.

Lemma has_predT : forall s, has predT s = (0 < size s).
Proof. by move=> s; rewrite has_count count_predT. Qed.

Lemma has_predC : forall a s, has (predC a) s = ~~ all a s.
Proof. by move=> a; elim=> //= x s ->; case (a x). Qed.

Lemma has_predU : forall a1 a2 s, has (predU a1 a2) s = has a1 s || has a2 s.
Proof.
by move=> a1 a2; elim=> //= [x s ->]; rewrite -!orbA; do !bool_congr.
Qed.

Lemma all_pred0 : forall s, all pred0 s = (size s == 0).
Proof. by move=> *; rewrite all_count count_pred0 eq_sym. Qed.

Lemma all_predT : forall s, all predT s = true.
Proof. by move=> *; rewrite all_count count_predT eqxx. Qed.

Lemma all_predC : forall a s, all (predC a) s = ~~ has a s.
Proof. by move=> a; elim=> //= x s ->; case (a x). Qed.

Lemma all_predI : forall a1 a2 s, all (predI a1 a2) s = all a1 s && all a2 s.
Proof.
move=> a1 a2 s; apply: can_inj negb negbK _ _ _.
rewrite negb_andb -!has_predC -has_predU; apply: eq_has => x.
by rewrite /= negb_andb.
Qed.

(* Surgery: drop, take, rot, rotr.                                        *)

Fixpoint drop n s {struct s} :=
  match s, n with
  | _ :: s', n'.+1 => drop n' s'
  | _, _ => s
  end.

Lemma drop_behead : drop n0 =1 iter n0 behead.
Proof. by elim: n0 => [|n IHn] [|x s] //; rewrite iterSr -IHn. Qed.

Lemma drop0 : forall s, drop 0 s = s. Proof. by case. Qed.

Lemma drop1 : drop 1 =1 behead. Proof. by move=> [|x [|y s]]. Qed.

Lemma drop_oversize : forall n s, size s <= n -> drop n s = [::].
Proof. by elim=> [|n IHn] [|x s]; try exact (IHn s). Qed.

Lemma drop_size : forall s, drop (size s) s = [::].
Proof. by move=> s; rewrite drop_oversize // leqnn. Qed.

Lemma drop_cons : forall x s,
  drop n0 (x :: s) = if n0 is n.+1 then drop n s else x :: s.
Proof. by []. Qed.

Lemma size_drop : forall s, size (drop n0 s) = size s - n0.
Proof. by move=> s; elim: s n0 => [|x s IHs] [|n]; try exact (IHs n). Qed.

Lemma drop_cat : forall s1 s2,
 drop n0 (s1 ++ s2) =
   if n0 < size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2.
Proof.
by move=> s1 s2; elim: s1 n0 => [|x s1 IHs] [|n]; try exact (IHs n).
Qed.

Lemma drop_size_cat : forall n s1 s2, size s1 = n -> drop n (s1 ++ s2) = s2.
Proof. by move=> _ s1 s2 <-; elim: s1 => [|x s1 IHs] //=; rewrite drop0. Qed.

Lemma nconsK : forall n x, cancel (ncons n x) (drop n).
Proof. by move=> n x; elim: n => // [] []. Qed.

Fixpoint take n s {struct s} :=
  match s, n with
  | x :: s', n'.+1 => x :: take n' s'
  | _, _ => [::]
  end.

Lemma take0 : forall s, take 0 s = [::]. Proof. by case. Qed.

Lemma take_oversize : forall n s, size s <= n -> take n s = s.
Proof. by elim=> [|n IHn] [|x s] Hsn; try (congr Cons; apply: IHn). Qed.

Lemma take_size : forall s, take (size s) s = s.
Proof. by move=> s; rewrite take_oversize // leqnn. Qed.

Lemma take_cons : forall x s,
  take n0 (x :: s) = if n0 is n.+1 then x :: (take n s) else [::].
Proof. by []. Qed.

Lemma drop_rcons : forall s, n0 <= size s ->
  forall x, drop n0 (rcons s x) = rcons (drop n0 s) x.
Proof. by move=> s; elim: s n0 => [|y s IHs] [|n]; try exact (IHs n). Qed.

Lemma cat_take_drop : forall s, take n0 s ++ drop n0 s = s.
Proof.
by move=> s; elim: s n0 => [|x s IHs] [|n]; try exact (congr1 _ (IHs n)).
Qed.

Lemma size_takel : forall s, n0 <= size s -> size (take n0 s) = n0.
Proof.
move=> s; move/subnKC; rewrite -{2}(cat_take_drop s) size_cat size_drop.
by move/addIn.
Qed.

Lemma size_take : forall s,
  size (take n0 s) = if n0 < size s then n0 else size s.
Proof.
move=> s; case: (ltnP n0 (size s));
 last by move=> *; rewrite take_oversize.
by move=> *; apply size_takel; apply ltnW.
Qed.

Lemma take_cat : forall s1 s2,
 take n0 (s1 ++ s2) =
   if n0 < size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2.
Proof.
move=> s1 s2; elim: s1 n0 => [|x s1 IHs] [|n] //=.
by rewrite ltnS subSS -(fun_if (cons x)) -IHs.
Qed.

Lemma take_size_cat : forall n s1 s2, size s1 = n -> take n (s1 ++ s2) = s1.
Proof.
by move=> _ s1 s2 <-; elim: s1 => [|x s1 IHs]; rewrite ?take0 //= IHs.
Qed.

Lemma takel_cat : forall s1, n0 <= size s1 ->
  forall s2, take n0 (s1 ++ s2) = take n0 s1.
Proof.
move=> s1 Hn0 s2; rewrite take_cat ltn_neqAle Hn0 andbT.
case: (n0 =P size s1) => [Dn0|_] //.
by rewrite Dn0 subnn take0 cats0 take_size.
Qed.

Lemma nth_drop : forall s i, nth (drop n0 s) i = nth s (n0 + i).
Proof.
move=> s i; case: (ltnP n0 (size s)) => [Hn|Hn].
  rewrite -{2}[s]cat_take_drop nth_cat size_take Hn /=.
  by rewrite ltnNge leq_addr addKn.
rewrite !nth_default //; first by apply: (leq_trans Hn); apply: leq_addr.
by rewrite -subn_eq0 in Hn; rewrite size_drop (eqP Hn) leq0n.
Qed.

Lemma nth_take : forall i, i < n0 -> forall s, nth (take n0 s) i = nth s i.
Proof.
move=> i Hi s; case Hn: (n0  < size s).
  by rewrite -{2}[s]cat_take_drop nth_cat size_take Hn /= Hi.
by rewrite -{1}[s]cats0 take_cat Hn /= cats0.
Qed.

(* drop_nth and take_nth below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the nth default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_nth : forall n s, n < size s -> drop n s = nth s n :: drop n.+1 s.
Proof.
by move=> n s; elim: s n => [|x s IHs] [|n] Hn //=; rewrite ?drop0 1?IHs.
Qed.

Lemma take_nth : forall n s, n < size s ->
  take n.+1 s = rcons (take n s) (nth s n).
Proof.
by move=> n s; elim: s n => [|x s IHs] //= [|n] Hn /=; rewrite ?take0 -?IHs.
Qed.

Definition rot n s := drop n s ++ take n s.

Lemma rot0 : forall s, rot 0 s = s.
Proof. by move=> *; rewrite /rot drop0 take0 cats0. Qed.

Lemma size_rot : forall s, size (rot n0 s) = size s.
Proof. by move=> s; rewrite -{2}[s]cat_take_drop /rot !size_cat addnC. Qed.

Lemma rot_oversize : forall n s, size s <= n -> rot n s = s.
Proof.
by move=> n s Hn; rewrite /rot (take_oversize Hn) (drop_oversize Hn).
Qed.

Lemma rot_size : forall s, rot (size s) s = s.
Proof. exact (fun s => rot_oversize (leqnn _)). Qed.

Lemma has_rot : forall s a, has a (rot n0 s) = has a s.
Proof. by move=> *; rewrite has_cat orbC -has_cat cat_take_drop. Qed.

Lemma rot_size_cat : forall s1 s2, rot (size s1) (s1 ++ s2) = s2 ++ s1.
Proof. by move=> s1 s2; rewrite /rot take_size_cat ?drop_size_cat. Qed.

Definition rotr n s := rot (size s - n) s.

Lemma rotK : cancel (rot n0) (rotr n0).
Proof.
move=> s; rewrite /rotr size_rot -size_drop {2}/rot.
by rewrite rot_size_cat cat_take_drop.
Qed.

Lemma rot_inj : injective (rot n0). Proof. exact (can_inj rotK). Qed.

Lemma rot1_cons : forall x s, rot 1 (x :: s) = rcons s x.
Proof. by move=> *; rewrite /rot /= take0 drop0 -cats1. Qed.

(* (efficient) reversal *)

Fixpoint catrev s2 s1 {struct s1} :=
  if s1 is x :: s1' then catrev (x :: s2) s1' else s2.

End Sequences.

(* rev must be defined outside a Section because Coq's end of section *)
(* "cooking" removes the nosimpl guard.                               *)

Definition rev T s := nosimpl catrev T (Nil T) s.

Prenex Implicits size head ohead behead last rcons belast.
Prenex Implicits cat take drop rev rot rotr.
Prenex Implicits find count nth all has filter.

Notation "s1 ++ s2" := (cat s1 s2) : seq_scope.

Section Rev.

Variable T : Type.
Implicit Type s : seq T.

Lemma rev_rcons : forall s x, rev (rcons s x) = x :: (rev s).
Proof. by move=> s x; rewrite /rev -cats1 /=; elim: s {-2}[::] => /=. Qed.

Lemma rev_cons : forall x s, rev (x :: s) = rcons (rev s) x.
Proof.
move=> x; elim/last_ind=> [|s y IHs] //.
by rewrite rev_rcons /= -IHs -rev_rcons.
Qed.

Lemma size_rev : forall s, size (rev s) = size s.
Proof. by elim=> [|x s IHs] //; rewrite rev_cons size_rcons IHs. Qed.

Lemma rev_cat : forall s1 s2, rev (s1 ++ s2) = rev s2 ++ rev s1.
Proof.
move=> s1 s2; elim: s1 => [|x s1 IHs] /=; first by rewrite cats0.
by rewrite !rev_cons IHs -!cats1 catA.
Qed.

Lemma revK : involutive (@rev T).
Proof. by elim=> [|x s IHs] //=; rewrite rev_cons rev_rcons IHs. Qed.

Lemma nth_rev : forall x0 n s,
  n < size s -> nth x0 (rev s) n = nth x0 s (size s - n.+1).
Proof.
move=> x0 n s; elim/last_ind: s n => [|s x IHs] n //.
rewrite rev_rcons size_rcons ltnS subSS -cats1 nth_cat /=.
case: n => [|n] Hn; first by rewrite subn0 ltnn subnn.
by rewrite -{2}(subnK Hn) -addSnnS leq_addr /= -IHs.
Qed.

End Rev.

(* Equality and eqType for seq.                                          *)

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Notation Local nth := (nth x0).
Implicit Type s : seq T.
Implicit Types x y z : T.

Fixpoint eqseq s1 s2 {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : Equality.axiom eqseq.
Proof.
move; elim=> [|x1 s1 IHs] [|x2 s2]; do [ by constructor | simpl ].
case: (x1 =P x2) => [<-|neqx]; last by right; case.
by apply: (iffP (IHs _)) => [<-|[]].
Qed.

Canonical Structure seq_eqMixin := EqMixin eqseqP.
Canonical Structure seq_eqType := Eval hnf in EqType seq_eqMixin.

Lemma eqseqE : eqseq = eq_op. Proof. by []. Qed.

Lemma eqseq_cons : forall x1 x2 s1 s2,
  (x1 :: s1 == x2 :: s2) = (x1 == x2) && (s1 == s2).
Proof. by []. Qed.

Lemma eqseq_cat : forall s1 s2 s3 s4,
  size s1 = size s2 -> (s1 ++ s3 == s2 ++ s4) = (s1 == s2) && (s3 == s4).
Proof.
move=> s1 s2 s3 s4 sz12; elim: s1 s2 sz12 => [|x1 s1 IHs] [|x2 s2] //= [sz12].
by rewrite !eqseq_cons -andbA IHs.
Qed.

Lemma eqseq_rcons : forall s1 s2 x1 x2,
  (rcons s1 x1 == rcons s2 x2) = (s1 == s2) && (x1 == x2).
Proof.
move=> s1 s2 x1 x2; elim: s1 s2 => [|y1 s1 IHs] [|y2 s2];
  rewrite /= ?eqseq_cons ?andbT ?andbF // ?IHs 1?andbA // andbC;
  by [ case s2 | case s1 ].
Qed.

Lemma has_filter : forall a s, has a s = (filter a s != [::]).
Proof. by move=> a s; rewrite has_count count_filter; case (filter a s). Qed.

Lemma size_eq0 : forall s, (size s == 0) = (s == [::]).
Proof. move=> s; apply/eqP/eqP=> [|-> //]; exact: size0nil. Qed.

(* mem_seq and index. *)
(* mem_seq defines a predType for seq. *)

Fixpoint mem_seq (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

Definition eqseq_class := seq T.
Identity Coercion seq_of_eqseq : eqseq_class >-> seq.

Coercion pred_of_eq_seq (s : eqseq_class) : pred_class := [eta mem_seq s].

Canonical Structure seq_predType := @mkPredType T (seq T) pred_of_eq_seq.
(* The line below makes mem_seq a canonical instance of topred. *)
Canonical Structure mem_seq_predType := mkPredType mem_seq.

Lemma in_cons : forall y s x, (x \in y :: s) = (x == y) || (x \in s).
Proof. by []. Qed.

Lemma in_nil : forall x, (x \in [::]) = false.
Proof. by []. Qed.

Lemma mem_seq1 : forall x y, (x \in [:: y]) = (x == y).
Proof. by move=> x y; rewrite in_cons orbF. Qed.

 (* to be repeated after the Section discharge. *)
Let inE := (mem_seq1, in_cons, inE).

Lemma mem_seq2 : forall x y1 y2, (x \in [:: y1; y2]) = xpred2 y1 y2 x.
Proof. by move=> x y1 y2; rewrite !inE. Qed.

Lemma mem_seq3 :  forall x y1 y2 y3,
  (x \in [:: y1; y2; y3]) = xpred3 y1 y2 y3 x.
Proof. by move=> x y1 y2 y3; rewrite !inE. Qed.

Lemma mem_seq4 :  forall x y1 y2 y3 y4,
  (x \in [:: y1; y2; y3; y4]) = xpred4 y1 y2 y3 y4 x.
Proof. by move=> x y1 y2 y3 y4; rewrite !inE. Qed.

Lemma mem_cat : forall x s1 s2, (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof.
by move=> x s1 s2; elim: s1 => //= y s1 IHs; rewrite !inE /= -orbA -IHs.
Qed.

Lemma mem_rcons : forall s y, rcons s y =i y :: s.
Proof. by move=> s y x; rewrite -cats1 /= mem_cat mem_seq1 orbC in_cons. Qed.

Lemma mem_head : forall x s, x \in x :: s.
Proof. by move=> *; exact: predU1l. Qed.

Lemma mem_last : forall x s, last x s \in x :: s.
Proof. by move=> *; rewrite lastI mem_rcons mem_head. Qed.

Lemma mem_behead : forall s, {subset behead s <= s}.
Proof.  move=> [|y s] x //; exact: predU1r. Qed.

Lemma mem_belast : forall s y, {subset belast y s <= y :: s}.
Proof. by move=> s y x ys'x; rewrite lastI mem_rcons mem_behead. Qed.

Lemma mem_nth : forall s n, n < size s -> nth s n \in s.
Proof.
by elim=> [|x s IHs] // [_|n sz_s]; rewrite ?mem_head // mem_behead ?IHs.
Qed.

Lemma mem_take : forall s x, x \in take n0 s -> x \in s.
Proof. by move=> s x Hx; rewrite -(cat_take_drop n0 s) mem_cat /= Hx. Qed.

Lemma mem_drop : forall s x, x \in drop n0 s -> x \in s.
Proof. by move=> s x Hx; rewrite -(cat_take_drop n0 s) mem_cat /= Hx orbT. Qed.

Lemma mem_rev : forall s, rev s =i s.
Proof.
move=> s y; elim: s => [|x s IHs] //.
by rewrite rev_cons /= mem_rcons in_cons IHs.
Qed.

Section Filters.

Variable a : pred T.

Lemma hasP : forall s, reflect (exists2 x, x \in s & a x) (has a s).
Proof.
elim=> [|y s IHs] /=; first by right; case.
case ay: (a y); first by left; exists y; rewrite ?mem_head.
apply: (iffP IHs) => [] [x ysx ax]; exists x => //; first exact: mem_behead.
by case: (predU1P ysx) ax => [->|//]; rewrite ay.
Qed.

Lemma hasPn : forall s, reflect (forall x, x \in s -> ~~ a x) (~~ has a s).
Proof.
move=> s; apply: (iffP idP) => [Hs x Hx|Hs].
  by apply/negPn => Hax; case: (elimN (hasP _) Hs); exists x.
by apply/hasP=> [] [x Hx Hax]; case (negP (Hs _ Hx)).
Qed.

Lemma allP : forall s, reflect (forall x, x \in s -> a x) (all a s).
Proof.
elim=> [|x s IHs]; first by left.
rewrite /= andbC; case: IHs => IHs /=.
  apply: (iffP idP) => [Hx y|]; last by apply; exact: mem_head.
  by case/predU1P=> [->|Hy]; auto.
by right; move=> H; case IHs; move=> y Hy; apply H; exact: mem_behead.
Qed.

Lemma allPn : forall s, reflect (exists2 x, x \in s & ~~ a x) (~~ all a s).
Proof.
elim=> [|x s IHs]; first by right; move=> [x Hx _].
rewrite /= andbC negb_andb; case: IHs => [IHs|IHs]; simpl.
  by left; case: IHs => y Hy Hay; exists y; first exact: mem_behead.
case Hax: (a x); constructor; last by exists x; rewrite ?Hax ?inE /= ?eqxx.
move=> [y Hy Hay]; case IHs; exists y; last by [].
by case/predU1P: Hy Hay => [->|Hy]; first by rewrite Hax.
Qed.

Lemma mem_filter : forall x s, (x \in filter a s) = a x && (x \in s).
Proof.
move=> x s; rewrite /= andbC; elim: s => [|y s IHs] //=.
rewrite (fun_if (fun s' : seq T => x \in s')) !in_cons {}IHs.
by case: eqP => [->|_]; case (a y); rewrite /= ?andbF.
Qed.

End Filters.

Lemma eq_in_filter : forall (a1 a2 : pred T) s,
  {in s, a1 =1 a2} -> filter a1 s = filter a2 s.
Proof.
move=> a1 a2; elim => [| x s IHs eq_a] //=.
rewrite eq_a ?mem_head ?IHs // => y s_y; apply: eq_a; exact: mem_behead.
Qed.

Lemma eq_has_r : forall s1 s2, s1 =i s2 -> has^~ s1 =1 has^~ s2.
Proof.
move=> s1 s2 Es12 a; apply/(hasP a s1)/(hasP a s2) => [] [x Hx Hax];
 by exists x; rewrite // ?Es12 // -Es12.
Qed.

Lemma eq_all_r : forall s1 s2, s1 =i s2 -> all^~ s1 =1 all^~ s2.
Proof.
by move=> s1 s2 Es12 a; apply/(allP a s1)/(allP a s2) => Hs x Hx;
  apply Hs; rewrite Es12 in Hx *.
Qed.

Lemma has_sym : forall s1 s2, has (mem s1) s2 = has (mem s2) s1.
Proof.
by move=> s1 s2; apply/(hasP _ s2)/(hasP _ s1) => [] [x]; exists x.
Qed.

Lemma has_pred1 : forall x s, has (pred1 x) s = (x \in s).
Proof. by move=> x s; rewrite -(eq_has (mem_seq1^~ x)) has_sym /= orbF. Qed.

(* Constant sequences, i.e., the image of nseq. *)

Definition constant s := if s is x :: s' then all (pred1 x) s' else true.

Lemma all_pred1P : forall x s, reflect (s = nseq (size s) x) (all (pred1 x) s).
Proof.
move=> x; elim=> [|y s IHs] /=; first by left.
case: eqP => [->{y} | ne_xy]; last by right=> [] [? _]; case ne_xy.
by apply: (iffP IHs) => [<- //| []].
Qed.

Lemma all_pred1_constant : forall x s, all (pred1 x) s -> constant s.
Proof. by move=> x [|y s] //=; case/andP; move/eqP->. Qed.

Lemma all_pred1_nseq : forall x y n,
  all (pred1 x) (nseq n y) = (n == 0) || (x == y).
Proof.
move=> a x [|n] //=; rewrite eq_sym; case: eqP => // -> {y}.
by elim: n => //= n ->; rewrite eqxx.
Qed.
 
Lemma constant_nseq : forall n x, constant (nseq n x).
Proof. by case=> //= n x; rewrite all_pred1_nseq eqxx orbT. Qed.

(* Uses x0 *)
Lemma constantP : forall s,
  reflect (exists x, s = nseq (size s) x) (constant s).
Proof.
move=> s; apply: (iffP idP) => [| [x ->]]; last exact: constant_nseq.
case: s => [|x s] /=; first by exists x0.
by move/all_pred1P=> def_s; exists x; rewrite -def_s.
Qed.

(* Duplicate-freenes. *)

Fixpoint uniq s :=
  if s is x :: s' then (x \notin s') && uniq s' else true.

Lemma cons_uniq : forall x s, uniq (x :: s) = (x \notin s) && uniq s.
Proof. by []. Qed.

Lemma cat_uniq : forall s1 s2,
  uniq (s1 ++ s2) = [&& uniq s1, ~~ has (mem s1) s2 & uniq s2].
Proof.
move=> s1 s2; elim: s1 => [|x s1 IHs]; first by rewrite /= has_pred0.
by rewrite has_sym /= mem_cat !negb_orb has_sym IHs -!andbA; do !bool_congr.
Qed.

Lemma uniq_catC : forall s1 s2, uniq (s1 ++ s2) = uniq (s2 ++ s1).
Proof. by move=> *; rewrite !cat_uniq has_sym andbCA andbA andbC. Qed.

Lemma uniq_catCA : forall s1 s2 s3,
  uniq (s1 ++ s2 ++ s3) = uniq (s2 ++ s1 ++ s3).
Proof.
move=> s1 s2 s3.
by rewrite !catA -!(uniq_catC s3) !(cat_uniq s3) uniq_catC !has_cat orbC.
Qed.

Lemma rcons_uniq : forall s x, uniq (rcons s x) = (x \notin s) && uniq s.
Proof. by move=> *; rewrite -cats1 uniq_catC. Qed.

Lemma filter_uniq : forall s a, uniq s -> uniq (filter a s).
Proof.
move=> s a; elim: s => [|x s IHs] //=; case/andP=> [Hx Hs]; case (a x); auto.
by rewrite /= mem_filter /= (negbTE Hx) andbF; auto.
Qed.

Lemma rot_uniq : forall s, uniq (rot n0 s) = uniq s.
Proof. by move=> *; rewrite /rot uniq_catC cat_take_drop. Qed.

Lemma rev_uniq : forall s, uniq (rev s) = uniq s.
Proof.
elim=> // x s IHs.
by rewrite rev_cons -cats1 cat_uniq /= andbT andbC mem_rev orbF IHs.
Qed.

Lemma count_uniq_mem : forall s x, uniq s -> count (pred1 x) s = (x \in s).
Proof.
move=> s x; elim: s => //= [y s IHs]; case/andP; move/negbTE => Hy Us.
by rewrite {}IHs {Us}// in_cons eq_sym; case: eqP => // ->; rewrite Hy.
Qed.

(* Removing duplicates *)

Fixpoint undup s :=
  if s is x :: s' then if x \in s' then undup s' else x :: undup s' else [::].

Lemma size_undup : forall s, size (undup s) <= size s.
Proof. elim=> //= [x s IHs]; case: (x \in s) => //=; exact: ltnW. Qed.

Lemma mem_undup : forall s, undup s =i s.
Proof.
move=> s x; elim: s => //= [y s IHs].
by case Hy: (y \in s); rewrite in_cons IHs //; case: eqP => // ->.
Qed.

Lemma undup_uniq : forall s, uniq (undup s).
Proof.
by elim=> //= [x s IHs]; case Hx: (x \in s); rewrite //= mem_undup Hx.
Qed.

Lemma undup_id : forall s, uniq s -> undup s = s.
Proof. by elim=> //= [x s IHs]; case/andP; move/negbTE->; move/IHs->. Qed.

Lemma ltn_size_undup : forall s, (size (undup s) < size s) = ~~ uniq s.
Proof.
by elim=> //= [x s IHs]; case Hx: (x \in s); rewrite //= ltnS size_undup.
Qed. 

(* Lookup *)

Definition index x := find (pred1 x).

Lemma index_size : forall x s, index x s <= size s.
Proof. by move=> *; rewrite /index find_size. Qed.

Lemma index_mem : forall x s, (index x s < size s) = (x \in s).
Proof. by move=> *; rewrite -has_pred1 has_find. Qed.

Lemma nth_index : forall x s, x \in s -> nth s (index x s) = x.
Proof. by move=> x s; rewrite -has_pred1; move/(nth_find x0); move/eqP. Qed.

Lemma index_cat : forall x s1 s2,
 index x (s1 ++ s2) = if x \in s1 then index x s1 else size s1 + index x s2.
Proof. by move=> x s1 s2; rewrite /index find_cat has_pred1. Qed.

Lemma index_uniq : forall i s, i < size s -> uniq s -> index (nth s i) s = i.
Proof.
move=> i s; simpl; elim: s i => [|x s IHs] //= [|i]; rewrite /= ?eqxx // ltnS.
move=> Hi; case/andP=> [Hx Hs]; rewrite (IHs i Hi Hs).
by case: eqP Hx => [->|_]; first by rewrite mem_nth.
Qed.

Lemma index_head : forall x s, index x (x :: s) = 0.
Proof. by move=> *; rewrite /= eqxx. Qed.

Lemma index_last : forall x s,
  uniq (x :: s) -> index (last x s) (x :: s) = size s.
Proof.
move=> x s; rewrite lastI rcons_uniq -cats1 index_cat size_belast.
by case: (_ \in _) => //=; rewrite eqxx addn0.
Qed.

Lemma nth_uniq : forall s i j,
   i < size s -> j < size s -> uniq s -> (nth s i == nth s j) = (i == j).
Proof.
move => s i j Hi Hj Us; apply/eqP/eqP=> [eq_sij|-> //].
by rewrite -(index_uniq Hi Us) eq_sij index_uniq.
Qed.

Lemma mem_rot : forall s, rot n0 s =i s.
Proof. by move=> s x; rewrite -{2}(cat_take_drop n0 s) !mem_cat /= orbC. Qed.

Lemma eqseq_rot : forall s1 s2, (rot n0 s1 == rot n0 s2) = (s1 == s2).
Proof. apply: inj_eq; exact: rot_inj. Qed.

CoInductive rot_to_spec (s : seq T) (x : T) : Type :=
  RotToSpec i s' of rot i s = x :: s'.

Lemma rot_to : forall s x, x \in s -> rot_to_spec s x.
Proof.
move=> s x sx; pose i := index x s; exists i (drop i.+1 s ++ take i s).
rewrite -cat_cons {}/i; congr cat; elim: s sx => //= y s IHs.
by rewrite eq_sym in_cons; case: eqP => // -> _; rewrite drop0.
Qed.

End EqSeq.

Definition inE := (mem_seq1, in_cons, inE).

Prenex Implicits uniq undup index.

Implicit Arguments eqseqP [T x y].
Implicit Arguments all_filterP [T a s].
Implicit Arguments hasP [T a s].
Implicit Arguments hasPn [T a s].
Implicit Arguments allP [T a s].
Implicit Arguments allPn [T a s].
Prenex Implicits eqseqP all_filterP hasP hasPn allP allPn.

Section NseqthTheory.

Lemma nthP : forall (T : eqType) (s : seq T) x x0,
  reflect (exists2 i, i < size s & nth x0 s i = x) (x \in s).
Proof.
move=> T s x x0; apply: (iffP idP) => [|[n Hn <-]]; last by apply mem_nth.
by exists (index x s); [ rewrite index_mem | apply nth_index ].
Qed.

Variable T : Type.

Lemma has_nthP : forall (a : pred T) s x0,
  reflect (exists2 i, i < size s & a (nth x0 s i)) (has a s).
Proof.
move=> a s x0; elim: s => [|x s IHs] /=; first by right; case.
case nax: (a x); first by left; exists 0.
by apply: (iffP IHs) => [[i]|[[|i]]]; [exists i.+1 | rewrite nax | exists i].
Qed.

Lemma all_nthP : forall (a : pred T) s x0,
  reflect (forall i, i < size s -> a (nth x0 s i)) (all a s).
Proof.
move=> a s x0; rewrite -(eq_all (fun x => negbK (a x))) all_predC.
case: (has_nthP _ _ x0) => [na_s | a_s]; [right=> a_s | left=> i lti].
  by case: na_s => i lti; rewrite a_s.
by apply/idPn=> na_si; case: a_s; exists i.
Qed.

End NseqthTheory.

Lemma set_nth_default : forall T s (y0 x0 : T) n,
  n < size s -> nth x0 s n = nth y0 s n.
Proof. by move=> T s y0 x0; elim: s => [|y s' IHs] [|n] /=; auto. Qed.

Lemma headI : forall T s (x : T),
  rcons s x = head x s :: behead (rcons s x).
Proof. by move=> T []. Qed.

Implicit Arguments nthP [T s x].
Implicit Arguments has_nthP [T a s].
Implicit Arguments all_nthP [T a s].
Prenex Implicits nthP has_nthP all_nthP.

Definition bitseq := seq bool.
Canonical Structure bitseq_eqType := Eval hnf in [eqType of bitseq].
Canonical Structure bitseq_predType := Eval hnf in [predType of bitseq].

(* Incrementing the ith nat in a seq nat, padding with 0's if needed. This  *)
(* allows us to use nat seqs as bags of nats.                               *)

Fixpoint incr_nth (v : seq nat) (i : nat) {struct i} : seq nat :=
  if v is n :: v' then
    if i is i'.+1 then n :: incr_nth v' i' else n.+1 :: v'
  else
    ncons i 0 [:: 1].

Lemma nth_incr_nth : forall v i j,
  nth 0 (incr_nth v i) j = (i == j) + nth 0 v j.
Proof.
elim=> [|n v IHv] [|i] [|j] //=; rewrite ?eqSS ?addn0 //; try by case j.
elim: i j => [|i IHv] [|j] //=; rewrite ?eqSS //; by case j.
Qed.

Lemma size_incr_nth : forall v i,
  size (incr_nth v i) = if i < size v then size v else i.+1.
Proof.
elim=> [|n v IHv] [|i] //=; first by rewrite size_ncons /= addn1.
rewrite IHv; exact: fun_if.
Qed.

(* equality up to permutation *)

Section PermSeq.

Variable T : eqType.

Definition same_count1 (s1 s2 : seq T) x :=
   count (pred1 x) s1 == count (pred1 x) s2.

Definition perm_eq (s1 s2 : seq T) := all (same_count1 s1 s2) (s1 ++ s2).

Lemma perm_eqP : forall s1 s2,
  reflect (count^~ s1 =1 count^~ s2) (perm_eq s1 s2).
Proof.
move=> s1 s2; apply: (iffP allP) => [eq_cnt1 a | eq_cnt x _]; last exact/eqP.
elim: {a}_.+1 {-2}a (ltnSn (count a (s1 ++ s2))) => // n IHn a le_an.
case: (posnP (count a (s1 ++ s2))).
  by move/eqP; rewrite count_cat addn_eq0; do 2 case: eqP => // ->.
rewrite -has_count; case/hasP=> x s12x a_x; pose a' := predD1 a x.
have cnt_a': forall s, count a s = count (pred1 x) s + count a' s.
  move=> s; rewrite count_filter -(count_predC (pred1 x)) 2!count_filter.
  rewrite -!filter_predI -!count_filter; congr (_ + _).
  by apply: eq_count => y /=; case: eqP => // ->.
rewrite !cnt_a'(eqnP (eq_cnt1 _ s12x)) (IHn a') // -ltnS.
apply: leq_trans le_an.
by rewrite ltnS cnt_a' -add1n leq_add2r -has_count has_pred1.
Qed.

Lemma perm_eq_refl : forall s, perm_eq s s.
Proof. by move=> s; exact/perm_eqP. Qed.
Hint Resolve perm_eq_refl.

Lemma perm_eq_sym : symmetric perm_eq.
Proof. by move=> s1 s2; apply/perm_eqP/perm_eqP=> ? ?. Qed.

Lemma perm_eq_trans : transitive perm_eq.
Proof.
move=> s2 s1 s3; move/perm_eqP=> eq12; move/perm_eqP=> eq23.
by apply/perm_eqP=> a; rewrite eq12.
Qed.

Notation perm_eql := (fun s1 s2 => perm_eq s1 =1 perm_eq s2).
Notation perm_eqr := (fun s1 s2 => perm_eq^~ s1 =1 perm_eq^~ s2).

Lemma perm_eqlP : forall s1 s2, reflect (perm_eql s1 s2) (perm_eq s1 s2).
Proof.
move=> s1 s2; apply: (iffP idP) => [eq12 s3 | -> //].
apply/idP/idP; last exact: perm_eq_trans.
by rewrite -!(perm_eq_sym s3); move/perm_eq_trans; apply.
Qed.

Lemma perm_eqrP : forall s1 s2, reflect (perm_eqr s1 s2) (perm_eq s1 s2).
Proof.
move=> s1 s2; apply: (iffP idP) => [| <- //].
by move/perm_eqlP=> eq12 s3; rewrite !(perm_eq_sym s3) eq12.
Qed.

Lemma perm_catC : forall s1 s2, perm_eql (s1 ++ s2) (s2 ++ s1).
Proof.
by move=> s1 s2; apply/perm_eqlP; apply/perm_eqP=> a; rewrite !count_cat addnC.
Qed.

Lemma perm_cat2l : forall s1 s2 s3,
  perm_eq (s1 ++ s2) (s1 ++ s3) = perm_eq s2 s3.
Proof.
move=> s1 s2 s3; apply/perm_eqP/perm_eqP=> eq23 a; apply/eqP;
  by move/(_ a): eq23; move/eqP; rewrite !count_cat eqn_addl.
Qed.

Lemma perm_cons : forall x s1 s2, perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.
Proof. move=> x; exact: (perm_cat2l [::x]). Qed.

Lemma perm_cat2r : forall s1 s2 s3,
  perm_eq (s2 ++ s1) (s3 ++ s1) = perm_eq s2 s3.
Proof.
move=> s1 s2 s3; do 2!rewrite perm_eq_sym perm_catC; exact: perm_cat2l.
Qed.

Lemma perm_catAC : forall s1 s2 s3,
  perm_eql ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof.
by move=> s1 s2 s3; apply/perm_eqlP; rewrite -!catA perm_cat2l perm_catC.
Qed.

Lemma perm_catCA : forall s1 s2 s3,
  perm_eql (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof.
by move=> s1 s2 s3; apply/perm_eqlP; rewrite !catA perm_cat2r perm_catC.
Qed.

Lemma perm_rcons : forall x s, perm_eql (rcons s x) (x :: s).
Proof. by move=> /= x s1 s2; rewrite -cats1 perm_catC. Qed.

Lemma perm_rot : forall n s, perm_eql (rot n s) s.
Proof. by move=> /= n s1 s2; rewrite perm_catC cat_take_drop. Qed.

Lemma perm_rotr : forall n s, perm_eql (rotr n s) s.
Proof. by move=> n s; exact: perm_rot. Qed.

Lemma perm_eq_mem : forall s1 s2, perm_eq s1 s2 -> s1 =i s2.
Proof.
by move=> s1 s2; move/perm_eqP=> eq12 x; rewrite -!has_pred1 !has_count eq12.
Qed.

Lemma perm_eq_size : forall s1 s2, perm_eq s1 s2 -> size s1 = size s2.
Proof. by move=> s1 s2; move/perm_eqP=> eq12; rewrite -!count_predT eq12. Qed.

Lemma uniq_leq_size : forall s1 s2 : seq T,
  uniq s1 -> {subset s1 <= s2} -> size s1 <= size s2.
Proof.
elim=> [|x s1 IHs] /= s2; [ by case s2 | move/andP=> [Hx Hs1] Hs12 ].
case: (@rot_to T s2 x); first by apply: Hs12; apply: predU1l.
move=> i s2' Ds2'; rewrite -(size_rot i s2) (Ds2'); apply: IHs => // [y /= Hy].
move: (Hs12 _ (predU1r _ _ Hy)); rewrite /= -(mem_rot i) Ds2'.
by case/predU1P=> // Dy; rewrite -Dy Hy in Hx.
Qed.

Lemma leq_size_uniq : forall s1 s2 : seq T,
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 -> uniq s2.
Proof.
elim=> [|x s1 IHs] s2 Hs1 Hs12; first by case s2.
case: (@rot_to T s2 x); [ by apply: Hs12; apply: predU1l | move=> i s2' Ds2' ].
  rewrite -(size_rot i) -(rot_uniq i) Ds2' /=; case Hs2': (x \in s2').
  rewrite ltnNge /=; case/negP; apply: (uniq_leq_size Hs1) => [y Hy].
  by move: (Hs12 _ Hy); rewrite /= -(mem_rot i) Ds2'; case/predU1P=> // ->.
move: Hs1 => /=; case/andP=> Hx Hs1; apply: IHs => // [y /= Hy].
have:= Hs12 _ (predU1r _ _ Hy); rewrite /= -(mem_rot i) Ds2'.
by case/predU1P=> // Dx; rewrite -Dx Hy in Hx.
Qed.

Lemma uniq_size_uniq : forall s1 s2 : seq T,
  uniq s1 -> s1 =i s2 -> uniq s2 = (size s2 == size s1).
Proof.
move=> s1 Hs1 s2 Es12.
rewrite eqn_leq andbC uniq_leq_size //=; last by move=> y /=; rewrite Es12.
apply/idP/idP => [Hs2|]; first by apply uniq_leq_size => // y; rewrite /= Es12.
by apply: leq_size_uniq => // y; rewrite /= Es12.
Qed.

Lemma leq_size_perm : forall s1 s2 : seq T,
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 ->
    s1 =i s2 /\ size s1 = size s2.
Proof.
move=> s1 s2 Us1 Hs1 Hs12; have Us2: uniq s2 by exact: leq_size_uniq Hs12.
suff: s1 =i s2 by split; last by apply/eqP; rewrite -uniq_size_uniq.
move=> x; apply/idP/idP=> [|Hxs2]; [exact: Hs1 | apply/idPn=> Hxs1].
suff: size (x :: s1) <= size s2 by rewrite /= ltnNge Hs12.
apply: uniq_leq_size => [|y] /=; first by rewrite Hxs1.
case/predU1P=> [-> //|]; exact: Hs1.
Qed.

Lemma perm_uniq : forall s1 s2 : seq T,
  s1 =i s2 -> size s1 = size s2 -> uniq s1 = uniq s2.
Proof.
move=> s1 s2 Es12 Hs12; apply/idP/idP => Us;
  by rewrite (uniq_size_uniq Us) ?Hs12 ?eqxx.
Qed.

Lemma perm_eq_uniq : forall s1 s2, perm_eq s1 s2 -> uniq s1 = uniq s2.
Proof.
move=> *; apply: perm_uniq; [exact: perm_eq_mem | exact: perm_eq_size].
Qed.

Lemma uniq_perm_eq : forall s1 s2,
  uniq s1 -> uniq s2 -> s1 =i s2 -> perm_eq s1 s2.
Proof.
move=> s1 s2 uniq1 uniq2 eq12; apply/allP=> x _; apply/eqP.
by rewrite !count_uniq_mem ?eq12.
Qed.

Lemma count_mem_uniq : forall s : seq T,
  (forall x, count (pred1 x) s = (x \in s)) -> uniq s.
Proof.
move=> s count1_s; have Uus := undup_uniq s.
suff: perm_eq s (undup s) by move/perm_eq_uniq->.
by apply/allP=> x _; apply/eqP; rewrite (count_uniq_mem x Uus) mem_undup.
Qed.

End PermSeq.

Notation perm_eql := (fun s1 s2 => perm_eq s1 =1 perm_eq s2).
Notation perm_eqr := (fun s1 s2 => perm_eq^~ s1 =1 perm_eq^~ s2).

Implicit Arguments perm_eqP [T s1 s2].
Implicit Arguments perm_eqlP [T s1 s2].
Implicit Arguments perm_eqrP [T s1 s2].
Prenex Implicits perm_eqP perm_eqlP perm_eqrP.
Hint Resolve perm_eq_refl.

Section RotrLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).

Lemma size_rotr : forall s : seq T, size (rotr n0 s) = size s.
Proof. by move=> *; rewrite size_rot. Qed.

Lemma mem_rotr : forall s : seq T', rotr n0 s =i s.
Proof. by move=> s x; rewrite mem_rot. Qed.

Lemma rotr_size_cat : forall s1 s2 : seq T,
  rotr (size s2) (s1 ++ s2) = s2 ++ s1.
Proof. by move=> *; rewrite /rotr size_cat addnK rot_size_cat. Qed.

Lemma rotr1_rcons : forall x (s : seq T), rotr 1 (rcons s x) = x :: s.
Proof. by move=> *; rewrite -rot1_cons rotK. Qed.

Lemma has_rotr : forall (a : pred T) s, has a (rotr n0 s) = has a s.
Proof. by move=> *; rewrite has_rot. Qed.

Lemma rotr_uniq : forall s : seq T', uniq (rotr n0 s) = uniq s.
Proof. by move=> *; rewrite rot_uniq. Qed.

Lemma rotrK : cancel (@rotr T n0) (rot n0).
Proof.
move=> s; case (ltnP n0 (size s)); move=> Hs.
rewrite -{1}(subKn (ltnW Hs)) -{1}[size s]size_rotr; first exact: rotK.
rewrite -{2}(rot_oversize Hs); rewrite -subn_eq0 in Hs.
by rewrite /rotr (eqP Hs) rot0.
Qed.

Lemma rotr_inj : injective (@rotr T n0).
Proof. exact (can_inj rotrK). Qed.

Lemma rev_rot : forall s : seq T, rev (rot n0 s) = rotr n0 (rev s).
Proof.
move=> s; rewrite /rotr size_rev -{3}(cat_take_drop n0 s) {1}/rot !rev_cat.
by rewrite -size_drop -size_rev rot_size_cat.
Qed.

Lemma rev_rotr : forall s : seq T, rev (rotr n0 s) = rot n0 (rev s).
Proof.
move=> s; apply: canRL rotrK _.
rewrite {1}/rotr size_rev size_rotr /rotr {2}/rot rev_cat.
set m := size s - n0; rewrite -{1}(@size_takel m _ _ (leq_subr _ _)).
by rewrite -size_rev rot_size_cat -rev_cat cat_take_drop.
Qed.

End RotrLemmas.

Section RotCompLemmas.

Variable T : Type.

Lemma rot_addn : forall m n (s : seq T), m + n <= size s ->
  rot (m + n) s = rot m (rot n s).
Proof.
move=> m n s; rewrite leq_eqVlt; case/predU1P=> [Emn|Hmn].
  by rewrite Emn rot_size -{1}(rotrK m s) /rotr -Emn addKn.
rewrite -{1}(cat_take_drop n s) /rot !take_cat !drop_cat.
rewrite addnC in Hmn; have Hn := leq_trans (leq_addr _ _) (ltnW Hmn).
rewrite (size_takel Hn) ltnNge leq_addl addnK /= catA.
by rewrite ltnNge size_drop leq_sub_add -ltnNge Hmn.
Qed.

Lemma rotS : forall n (s : seq T), n < size s -> rot n.+1 s = rot 1 (rot n s).
Proof. exact: rot_addn 1. Qed.

Lemma rot_add_mod : forall m n (s : seq T), n <= size s -> m <= size s ->
  rot m (rot n s) = rot (if m + n <= size s then m + n else m + n - size s) s.
Proof.
move=> m n s Hn Hm; case: leqP; [by move/rot_addn | move/ltnW=> Hmn].
symmetry.
by rewrite -{2}(rotK n s) /rotr -rot_addn size_rot addn_subA ?subnK ?addnK.
Qed.

Lemma rot_rot : forall m n (s : seq T), rot m (rot n s) = rot n (rot m s).
Proof.
move=> m n s; case: (ltnP (size s) m) => Hm.
  by rewrite !(@rot_oversize T m) ?size_rot 1?ltnW.
case: (ltnP (size s) n) => Hn.
  by rewrite !(@rot_oversize T n) ?size_rot 1?ltnW.
by rewrite !rot_add_mod 1?addnC.
Qed.

Lemma rot_rotr : forall m n (s : seq T), rot m (rotr n s) = rotr n (rot m s).
Proof. by move=> *; rewrite {2}/rotr size_rot rot_rot. Qed.

Lemma rotr_rotr : forall m n (s : seq T),
  rotr m (rotr n s) = rotr n (rotr m s).
Proof. by move=> *; rewrite /rotr !size_rot rot_rot. Qed.

End RotCompLemmas.

Section Sieve.

Variables (n0 : nat) (T : Type).

Fixpoint sieve (m : bitseq) (s : seq T) {struct m} : seq T :=
  match m, s with
  | b :: m', x :: s' => if b then x :: sieve m' s' else sieve m' s'
  | _, _ => [::]
  end.

Lemma sieve_false : forall s n, sieve (nseq n false) s = [::].
Proof. by elim=> [|x s IHs] [|n] /=. Qed.

Lemma sieve_true : forall s n, size s <= n -> sieve (nseq n true) s = s.
Proof. by elim=> [|x s IHs] [|n] //= Hn; congr Cons; apply: IHs. Qed.

Lemma sieve0 : forall m, sieve m [::] = [::].
Proof. by case. Qed.

Lemma sieve1 : forall b x, sieve [:: b] [:: x] = nseq b x.
Proof. by case. Qed.

Lemma sieve_cons : forall b m x s,
  sieve (b :: m) (x :: s) = nseq b x ++ sieve m s.
Proof. by case. Qed.

Lemma size_sieve : forall m s,
  size m = size s -> size (sieve m s) = count id m.
Proof. by elim=> [|b m IHm] [|x s] //= [Hs]; case: b; rewrite /= IHm. Qed.

Lemma sieve_cat : forall m1 s1, size m1 = size s1 ->
  forall m2 s2, sieve (m1 ++ m2) (s1 ++ s2) = sieve m1 s1 ++ sieve m2 s2.
Proof.
move=> m1 s1 Hm1 m2 s2; elim: m1 s1 Hm1 => [|b1 m1 IHm] [|x1 s1] //= [Hm1].
by rewrite (IHm _ Hm1); case b1.
Qed.

Lemma has_sieve_cons : forall a b m x s,
  has a (sieve (b :: m) (x :: s)) = b && a x || has a (sieve m s).
Proof. by move=> a [|]. Qed.

Lemma sieve_rot : forall m s, size m = size s ->
 sieve (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (sieve m s).
Proof.
move=> m s Hs; have Hsn0: (size (take n0 m) = size (take n0 s)).
  by rewrite !size_take Hs.
rewrite -(size_sieve Hsn0) {1 2}/rot sieve_cat ?size_drop ?Hs //.
rewrite -{4}(cat_take_drop n0 m) -{4}(cat_take_drop n0 s) sieve_cat //.
by rewrite rot_size_cat.
Qed.

End Sieve.

Section EqSieve.

Variables (n0 : nat) (T : eqType).

Lemma mem_sieve_cons : forall x b m y (s : seq T),
  (x \in sieve (b :: m) (y :: s)) = b && (x == y) || (x \in sieve m s).
Proof. by move=> x [|]. Qed.

Lemma mem_sieve : forall x m (s : seq T), (x \in sieve m s) -> (x \in s).
Proof.
by move=> x m s; elim: s m => [|y p IHs] [|[|] m] //=;
 rewrite !in_cons; case (x == y) => /=; eauto.
Qed.

Lemma sieve_uniq : forall s : seq T, uniq s -> forall m, uniq (sieve m s).
Proof.
elim=> [|x s IHs] /= Hs [|b m] //.
move/andP: Hs b => [Hx Hs] [|] /=; rewrite {}IHs // andbT.
apply/negP => [Hmx]; case/negP: Hx; exact (mem_sieve Hmx).
Qed.

Lemma mem_sieve_rot : forall m (s : seq T), size m = size s ->
  sieve (rot n0 m) (rot n0 s) =i sieve m s.
Proof. by move=> m s Hm x; rewrite sieve_rot // mem_rot. Qed.

End EqSieve.

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map (s : seq T1) : seq T2 :=
  if s is x :: s' then f x :: map s' else [::].

Lemma map_cons : forall x s, map (x :: s) = f x :: map s.
Proof. by []. Qed.

Lemma map_nseq : forall x, map (nseq n0 x) = nseq n0 (f x).
Proof. by move=> x; elim: n0 => // *; congr Cons. Qed.

Lemma map_cat : forall s1 s2, map (s1 ++ s2) = map s1 ++ map s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 IHs] //=; rewrite IHs. Qed.

Lemma size_map : forall s, size (map s) = size s.
Proof. by elim=> [|x s IHs] //=; rewrite IHs. Qed.

Lemma behead_map : forall s, behead (map s) = map (behead s).
Proof. by case. Qed.

Lemma nth_map : forall n s, n < size s -> nth x2 (map s) n = f (nth x1 s n).
Proof. by move=> n s; elim: s n => [|x s IHs] [|n]; try exact (IHs n). Qed.

Lemma map_rcons : forall s x,
  map (rcons s x) = rcons (map s) (f x).
Proof. by move=> *; rewrite -!cats1 map_cat. Qed.

Lemma last_map : forall s x, last (f x) (map s) = f (last x s).
Proof. by elim=> [|y s IHs] x /=. Qed.

Lemma belast_map : forall s x, belast (f x) (map s) = map (belast x s).
Proof. by elim=> [|y s IHs] x //=; rewrite IHs. Qed.

Lemma filter_map : forall a s,
  filter a (map s) = map (filter (preim f a) s).
Proof.
by move=> a; elim=> [|x s IHs] //=; rewrite (fun_if map) /= IHs.
Qed.

Lemma find_map : forall a s, find a (map s) = find (preim f a) s.
Proof. by move=> a; elim=> [|x s IHs] //=; rewrite IHs. Qed.

Lemma has_map : forall a s, has a (map s) = has (preim f a) s.
Proof. by move=> a; elim=> [|x s IHs] //=; rewrite IHs. Qed.

Lemma count_map : forall a s, count a (map s) = count (preim f a) s.
Proof. by move=> a; elim=> [|x s IHs] //=; rewrite IHs. Qed.

Lemma map_take : forall s, map (take n0 s) = take n0 (map s).
Proof. by elim: n0 => [|n IHn] [|x s] //=; rewrite IHn. Qed.

Lemma map_drop : forall s, map (drop n0 s) = drop n0 (map s).
Proof. by elim: n0 => [|n IHn] [|x s] //=; rewrite IHn. Qed.

Lemma map_rot : forall s, map (rot n0 s) = rot n0 (map s).
Proof. by move=> *; rewrite /rot map_cat map_take map_drop. Qed.

Lemma map_rotr : forall s, map (rotr n0 s) = rotr n0 (map s).
Proof.
by move=> *; apply: canRL (@rotK n0 T2) _; rewrite -map_rot rotrK.
Qed.

Lemma map_rev : forall s, map (rev s) = rev (map s).
Proof. by elim=> [|x s IHs] //=; rewrite !rev_cons -!cats1 map_cat IHs. Qed.

Lemma map_sieve : forall m s, map (sieve m s) = sieve m (map s).
Proof. by elim=> [|[|] m IHm] [|x p] //=; rewrite IHm. Qed.

Hypothesis Hf : injective f.

Lemma inj_map : injective map.
Proof.
move=> s1 s2; elim: s1 s2 => [|y1 s1 IHs] [|y2 s2] //= [Hy Hs].
by rewrite (Hf Hy) (IHs _ Hs).
Qed.

End Map.

Section EqMap.

Variables (n0 : nat) (T1 : eqType) (x1 : T1).
Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).

Lemma map_f : forall (s : seq T1) x, x \in s -> f x \in map f s.
Proof.
move=> s x; elim: s => [|y s IHs] //=.
by case/predU1P=> [->|Hx]; [ exact: predU1l | apply: predU1r; auto ].
Qed.

Lemma mapP : forall (s : seq T1) y,
  reflect (exists2 x, x \in s & y = f x) (y \in map f s).
Proof.
move=> s y; elim: s => [|x s IHs]; first by right; case.
rewrite /= in_cons eq_sym; case Hxy: (f x == y).
  by left; exists x; [ rewrite mem_head | rewrite (eqP Hxy) ].
apply: (iffP IHs) => [[x' Hx' ->]|[x' Hx' Dy]].
  by exists x'; first exact: predU1r.
by case: Dy Hxy => ->; case/predU1P: Hx' => [->|]; [rewrite eqxx | exists x'].
Qed.

Lemma map_uniq : forall s, uniq (map f s) -> uniq s.
Proof.
elim=> [|x s IHs] //=; case/andP=> [Hsx Hs]; rewrite (IHs Hs) andbT.
by apply/negP => Hx; case/mapP: Hsx; exists x.
Qed.

Lemma map_inj_in_uniq : forall s : seq T1,
  {in s &, injective f} -> uniq (map f s) = uniq s.
Proof.
elim=> //= x s IHs //= injf; congr (~~ _ && _).
  apply/mapP/idP=> [[y sy] |]; last by exists x.
  by move/injf=> ->; rewrite ?inE ?eqxx //= predU1r.
apply: IHs => y z sy sz; apply: injf => //; exact: predU1r.
Qed.

Hypothesis Hf : injective f.

Lemma mem_map : forall s x, (f x \in map f s) = (x \in s).
Proof. by move=> s x; apply/mapP/idP=> [[y Hy]|]; [move/Hf-> | exists x]. Qed.

Lemma index_map : forall s x, index (f x) (map f s) = index x s.
Proof.
move=> s x; rewrite /index; elim: s => [|y s IHs] //=.
by rewrite (inj_eq Hf) IHs.
Qed.

Lemma map_inj_uniq : forall s, uniq (map f s) = uniq s.
Proof. move=> s; apply: map_inj_in_uniq; exact: in2W. Qed.

End EqMap.

Implicit Arguments mapP [T1 T2 f s y].
Prenex Implicits mapP.

Lemma filter_sieve : forall T a (s : seq T), filter a s = sieve (map a s) s.
Proof. by move=> T a; elim=> //= [x s <-]; case: (a x). Qed.

Section MapComp.

Variable T1 T2 T3 : Type.

Lemma map_id : forall s : seq T1, map id s = s.
Proof. by elim=> [|x s IHs] //=; rewrite IHs. Qed.

Lemma eq_map : forall f1 f2 : T1 -> T2, f1 =1 f2 -> map f1 =1 map f2.
Proof. by move=> f1 f2 Ef; elim=> [|x s IHs] //=; rewrite Ef IHs. Qed.

Lemma map_comp : forall (f1 : T2 -> T3) (f2 : T1 -> T2) s,
  map (f1 \o f2) s = map f1 (map f2 s).
Proof. by move=> f1 f2; elim=> [|x s IHs] //=; rewrite IHs. Qed.

Lemma mapK : forall (f1 : T1 -> T2) (f2 : T2 -> T1),
  cancel f1 f2 -> cancel (map f1) (map f2).
Proof. by move=> f1 f2 Hf; elim=> [|x s IHs] //=; rewrite Hf IHs. Qed.

End MapComp.

Lemma eq_in_map : forall (T1 : eqType) T2 (f1 f2 : T1 -> T2) (s : seq T1),
  {in s, f1 =1 f2} -> map f1 s = map f2 s.
Proof.
move=> T1 T2 f1 f2; elim=> //= x s IHs eqf12.
rewrite eqf12 ?inE /= (eqxx, IHs) // => y sy.
by rewrite eqf12 ?inE //= predU1r.
Qed.

Lemma map_id_in : forall (T : eqType) f (s : seq T),
  {in s, f =1 id} -> map f s = s.
Proof. move=> T f s; move/eq_in_map->; exact: map_id. Qed.

(* Map a partial function *)

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then oapp (cons^~ (pmap s')) (pmap s') (f x) else [::].

Lemma map_pK : pcancel g f -> cancel (map g) pmap.
Proof. by move=> gK; elim=> //= x s ->; rewrite gK. Qed.

Lemma size_pmap : forall s, size (pmap s) = count [eta f] s.
Proof. by elim=> //= x s <-; case f. Qed.

Lemma pmapS_filter : forall s, map some (pmap s) = map f (filter [eta f] s).
Proof. by elim=> //= x s; case fx: (f x) => //= [u] <-; congr (_ :: _). Qed.

Hypothesis fK : ocancel f g.

Lemma pmap_filter : forall s, map g (pmap s) = filter [eta f] s.
Proof. by elim=> //= x s <-; rewrite -{3}(fK x); case f. Qed.

End Pmap.

Section EqPmap.

Variables (aT rT : eqType) (f : aT -> option rT) (g : rT -> aT).

Lemma eq_pmap : forall (f1 f2 : aT -> option rT),
 f1 =1 f2 -> pmap f1 =1 pmap f2.
Proof. by move=> f1 f2 Ef; elim=> [|x s IHs] //=; rewrite Ef IHs. Qed.

Lemma mem_pmap : forall s u, (u \in pmap f s) = (Some u \in map f s).
Proof.
by move=> s u; elim: s => //= x s IHs; rewrite in_cons -IHs; case (f x).
Qed.

Hypothesis fK : ocancel f g.

Lemma can2_mem_pmap : pcancel g f -> 
  forall s u, (u \in pmap f s) = (g u \in s).
Proof.
move=> gK s u.
by rewrite -(mem_map (pcan_inj gK)) pmap_filter // mem_filter gK.
Qed.

Lemma pmap_uniq : forall s, uniq s -> uniq (pmap f s).
Proof.
move=> s; move/(filter_uniq [eta f]); rewrite -(pmap_filter fK).
exact: map_uniq.
Qed.
 
End EqPmap.

Section Pmapub.

Variables (T : Type) (p : pred T) (sT : subType p).

Let insT : T -> option sT := insub.

Lemma size_pmap_sub : forall s, size (pmap insT s) = count p s.
Proof. by move=> s; rewrite size_pmap (eq_count (isSome_insub _)). Qed.

End Pmapub.

Section EqPmapSub.

Variables (T : eqType) (p : pred T) (sT : subType p).

Let insT : T -> option sT := insub.

Lemma mem_pmap_sub : forall (s : seq T) u,
  (u \in pmap insT s) = (val u \in s).
Proof. move=> s u; apply: (can2_mem_pmap (insubK _)); exact: valK. Qed.

Lemma pmap_sub_uniq : forall s : seq T, uniq s -> uniq (pmap insT s).
Proof. exact: (pmap_uniq (insubK _)). Qed.

End EqPmapSub.

(* Index sequence *)

Fixpoint iota (m n : nat) {struct n} : seq nat :=
  if n is n'.+1 then m :: iota m.+1 n' else [::].

Lemma size_iota : forall m n, size (iota m n) = n.
Proof. by move=> m n; elim: n m => //= [n IHn] m; rewrite IHn. Qed.

Lemma iota_add : forall m n1 n2,
  iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof.
move=> m n1 n2; elim: n1 m => //= [|n1 IHn1] m; first by rewrite addn0.
by rewrite -addSnnS -IHn1.
Qed.

Lemma iota_addl : forall m1 m2 n,
  iota (m1 + m2) n = map (addn m1) (iota m2 n).
Proof. by move=> m1 m2 n; elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.

Lemma nth_iota : forall m n i, i < n -> nth 0 (iota m n) i = m + i.
Proof.
move=> m n i Hi; rewrite -(subnKC Hi) addSnnS iota_add.
by rewrite nth_cat size_iota ltnn subnn.
Qed.

Lemma mem_iota : forall m n i, (i \in iota m n) = (m <= i) && (i < m + n).
Proof.
move=> m n i; elim: n m => [|n IHn] /= m.
  by rewrite addn0 ltnNge andb_negb_r.
rewrite -addSnnS leq_eqVlt in_cons eq_sym.
case: eqP => [->|_]; [by rewrite leq_addr | exact: IHn].
Qed.

Lemma iota_uniq : forall m n, uniq (iota m n).
Proof.
by move=> m n; elim: n m => //= [n IHn] m; rewrite mem_iota ltnn /=.
Qed.

(* Making a sequence of a specific length, using indexes to compute items. *)

Section MakeSeq.

Variables (T : Type) (x0 : T).

Definition mkseq f n : seq T := map f (iota 0 n).

Lemma size_mkseq : forall f n, size (mkseq f n) = n.
Proof. by move=> f n; rewrite /mkseq size_map size_iota. Qed.

Lemma eq_mkseq : forall f g, f =1 g -> mkseq f =1 mkseq g.
Proof. move=> f g Efg n; exact: eq_map Efg _. Qed.

Lemma nth_mkseq : forall f n i, i < n -> nth x0 (mkseq f n) i = f i.
Proof.
by move=> f n i Hi; rewrite /mkseq (nth_map 0) ?nth_iota ?size_iota.
Qed.

Lemma mkseq_nth : forall s, mkseq (nth x0 s) (size s) = s.
Proof.
move=> s; apply: (@eq_from_nth _ x0); rewrite size_mkseq // => i Hi.
by rewrite nth_mkseq.
Qed.

End MakeSeq.

Lemma mkseq_uniq : forall (T : eqType) (f : nat -> T) n,
  injective f -> uniq (mkseq f n).
Proof. by move=> *; rewrite /mkseq map_inj_uniq // iota_uniq. Qed.

Section FoldRight.

Variables (T R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr (s : seq T) : R := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Section FoldRightComp.

Variables (T1 T2 : Type) (h : T1 -> T2).
Variables (R : Type) (f : T2 -> R -> R) (z0 : R).

Lemma foldr_cat :
  forall s1 s2, foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
Proof. by move=> s1 s2; elim: s1 => [|x s1 IHs] //=; rewrite IHs. Qed.

Lemma foldr_map :
  forall s : seq T1, foldr f z0 (map h s) = foldr (fun x z => f (h x) z) z0 s.
Proof. by elim=> [|x s IHs] //=; rewrite IHs. Qed.

End FoldRightComp.

(* Quick characterization of the null sequence. *)

Definition sumn := foldr addn 0.

Lemma sumn_nseq : forall x n : nat, sumn (nseq n x) = x * n.
Proof. by move=> x n; rewrite mulnC; elim: n => //= n ->. Qed.

Lemma sumn_cat : forall s1 s2, sumn (s1 ++ s2) = sumn s1 + sumn s2.
Proof. by move=> s1 s2; elim: s1 => //= x s1 ->; rewrite addnA. Qed.

Lemma natnseq0P : forall s : seq nat,
  reflect (s = nseq (size s) 0) (sumn s == 0).
Proof.
move=> s; apply: (iffP idP) => [|->]; last by rewrite sumn_nseq.
elim: s => //= x s IHs; rewrite addn_eq0.
by case/andP; move/eqP->; move/IHs <-.
Qed.

Section FoldLeft.

Variables (T R : Type) (f : R -> T -> R).

Fixpoint foldl z (s : seq T) {struct s} :=
  if s is x :: s' then foldl (f z x) s' else z.

Lemma foldl_rev : forall z s, foldl z (rev s) = foldr (fun x z => f z x) z s.
Proof.
move=> z s; elim/last_ind: s z => [|s x IHs] z //=.
by rewrite rev_rcons -cats1 foldr_cat -IHs.
Qed.

Lemma foldl_cat : forall z s1 s2, foldl z (s1 ++ s2) = foldl (foldl z s1) s2.
Proof.
move=> z s1 s2; rewrite -(revK (s1 ++ s2)) foldl_rev rev_cat.
by rewrite foldr_cat -!foldl_rev !revK.
Qed.

End FoldLeft.

Section Scan.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Fixpoint pairmap x (s : seq T1) {struct s} :=
  if s is y :: s' then f x y :: pairmap y s' else [::].

Lemma size_pairmap : forall x s, size (pairmap x s) = size s.
Proof. by move=> x s; elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma nth_pairmap : forall s n, n < size s ->
  forall x, nth x2 (pairmap x s) n = f (nth x1 (x :: s) n) (nth x1 s n).
Proof. by elim=> [|y s IHs] [|n] //= Hn x; apply: IHs. Qed.

Fixpoint scanl x (s : seq T2) {struct s} :=
  if s is y :: s' then let x' := g x y in x' :: scanl x' s' else [::].

Lemma size_scanl : forall x s, size (scanl x s) = size s.
Proof. by move=> x s; elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma nth_scanl : forall s n, n < size s ->
  forall x, nth x1 (scanl x s) n = foldl g x (take n.+1 s).
Proof. by elim=> [|y s IHs] [|n] Hn x //=; rewrite ?take0 ?IHs. Qed.

Lemma scanlK :
  (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
Proof. by move=> Hfg x s; elim: s x => [|y s IHs] x //=; rewrite Hfg IHs. Qed.

Lemma pairmapK : 
  (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
Proof. by move=> Hgf x s; elim: s x => [|y s IHs] x //=; rewrite Hgf IHs. Qed.

End Scan.

Prenex Implicits sieve map pmap foldr foldl scanl pairmap.

Section Zip.

Variables T1 T2 : Type.

Fixpoint zip (s1 : seq T1) (s2 : seq T2) {struct s2} :=
  match s1, s2 with
  | x1 :: s1', x2 :: s2' => (x1,x2) :: zip s1' s2'
  | _, _ => [::]
  end.

Definition unzip1 := map (@fst T1 T2).
Definition unzip2 := map (@snd T1 T2).

Lemma zip_unzip : forall s, zip (unzip1 s) (unzip2 s) = s.
Proof. by elim=> [|[x1 x2] s /= ->]. Qed.

Lemma unzip1_zip : forall s1 s2,
  size s1 <= size s2 -> unzip1 (zip s1 s2) = s1.
Proof. by elim=> [|x1 s1 IHs] [|x2 s2] //= Ds; rewrite IHs. Qed.

Lemma unzip2_zip : forall s1 s2,
  size s2 <= size s1 -> unzip2 (zip s1 s2) = s2.
Proof. by elim=> [|x1 s1 IHs] [|x2 s2] //= Ds; rewrite IHs. Qed.

Lemma size1_zip : forall s1 s2,
  size s1 <= size s2 -> size (zip s1 s2) = size s1.
Proof. by elim=> [|x1 s1 IHs] [|x2 s2] //= Hs1; rewrite IHs. Qed.

Lemma size2_zip : forall s1 s2,
  size s2 <= size s1 -> size (zip s1 s2) = size s2.
Proof. by elim=> [|x1 s1 IHs] [|x2 s2] //= Hs1; rewrite IHs. Qed.

End Zip.

Prenex Implicits zip unzip1 unzip2.

Section Flatten.

Variable T : Type.

Definition flatten := foldr cat (Nil T).
Definition shape := map (@size T).
Fixpoint reshape (sh : seq nat) (s : seq T) {struct sh} :=
  if sh is n :: sh' then take n s :: reshape sh' (drop n s) else [::].

Lemma size_flatten : forall ss, size (flatten ss) = sumn (shape ss).
Proof. by elim=> //= s ss <-; rewrite size_cat. Qed.

Lemma flattenK : forall ss, reshape (shape ss) (flatten ss) = ss.
Proof.
by elim=> //= s ss IHss; rewrite take_size_cat ?drop_size_cat ?IHss.
Qed.

Lemma reshapeKr : forall sh s, size s <= sumn sh -> flatten (reshape sh s) = s.
Proof.
elim=> [[]|n sh IHsh] //= s sz_s; rewrite IHsh ?cat_take_drop //.
by rewrite size_drop leq_sub_add.
Qed.

Lemma reshapeKl : forall sh s, size s >= sumn sh -> shape (reshape sh s) = sh.
Proof.
elim=> [[]|n sh IHsh] //= s sz_s.
rewrite size_takel; last exact: leq_trans (leq_addr _ _) sz_s.
by rewrite IHsh // -(leq_add2l n) size_drop add_sub_maxn leq_maxr sz_s orbT.
Qed.

End Flatten.

Prenex Implicits flatten shape reshape.





