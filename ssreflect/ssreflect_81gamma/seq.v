(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import funs.
Require Import ssrbool.
Require Import eqtype.
Require Import ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Generic eqType seq : sequences of data items, essentially  polymorphic  *)
(* lists of data items, but with additional operations, such as finding    *)
(* items and indexing. Sequences need to be defined as a separate type,    *)
(* rather than an abbreviation for lists, because that abbreviation would  *)
(* be expanded out when doing elimination on a sequence.                   *)
(*   Since there is no true subtyping in Coq, we don't use a type for non  *)
(* empty sequences; rather, we pass explicitly the head and "tail" of the  *)
(* sequence.                                                               *)
(*   The empty sequence is especially bothersome for subscripting, since   *)
(* it forces us to have a default value. We use a combination of syntactic *)
(* extensions/prettyprinting to hide it in most of the development.        *)
(*   Here is the list of seq operations :                                  *)
(*   - constructors : Seq0, Adds (seq0, adds if polymorphic), add_last     *)
(*   - factories : addsn, seqn (repeat sequence), nseq (n-ary).            *)
(*   - items from indexes : iota (index generation), mkseq.                *)
(*   - access: behead, last, belast (the latter two for non empty seqs)    *)
(*   - indexing: head, sub (with a default element), incr_sub (for natseq) *)
(*   - size: size (seq version of length)                                  *)
(*   - elemets lookup: index, mem (which is a coercion)                    *)
(*   - subset lookup: find, filter, subfilter (filter to sub_eqType),      *)
(*                    count, has, all, sieve (filter by boolean mask)      *)
(*   - "no duplicates" predicate & function: uniq, undup                   *)
(*   - surgery: cat, drop, take, rot, rotr, rev                            *)
(*   - iterators: maps, foldr (= fold_right), foldl, scanl, pairmap        *)
(* The sieve operator uses a boolean sequence to select a subsequence; it  *)
(* is used heavily for the correctness of the config compilation.          *)
(* We are quite systematic in providing lemmas to rewrite any composition  *)
(* of two operations. "rev", whose simplifications are not natural, is     *)
(* protected with nosimpl.                                                 *)
(* We also define a (Seq ...) notation.                                    *)

Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

Reserved Notation "'Seq' x1"
  (at level 100, x1 at level 8, format "'Seq'  x1").

Reserved Notation "'Seq' x1 x2 .. y & s"
  (at level 100, x1, x2, y at level 8, s at level 10,
   format "'Seq'  x1  x2  ..  y  &  s").

Reserved Notation "'Seq' x1 x2 .. y"
  (at level 100, x1, x2, y at level 8, format "'Seq'  x1  x2  ..  y").

Reserved Notation "'Seq'" (at level 100).

Reserved Notation "'Seq' x1 & s"
  (at level 100, x1 at level 8, s at level 10, format "'Seq'  x1  &  s").

Section Sequences.

Variable n0 : nat.    (* numerical parameter for take, drop et al *)
Variable d : eqType.  (* must come before the implicit eqType     *)
Variable x0 : d.      (* default for head/sub *)

Inductive seq : Type := Seq0 | Adds (x : d) (s : seq).

Notation seq0 := Seq0. (* repeated after the end of section *)
Notation Local "'Seq' x" := (Adds x seq0).
Notation Local "'Seq' x1 x2 .. y" := (Adds x1 (Adds x2 .. (Seq y) ..)).

Fixpoint size (s : seq) : nat := if s is Adds _ s' then S (size s') else 0.

Definition head s := if s is Adds x _ then x else x0.

Definition behead s := if s is Adds _ s' then s' else Seq0.

Lemma size_behead : forall s, size (behead s) = pred (size s).
Proof. by case. Qed.

(* Equality and eqType for seq.                                          *)

Fixpoint eqseq (s1 s2 : seq) {struct s2} : bool :=
  match s1, s2 with
  | Seq0, Seq0 => true
  | Adds x1 s1', Adds x2 s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : reflect_eq eqseq.
Proof.
move; elim=> [|x1 s1 Hrec] [|x2 s2]; first [ by constructor | simpl ].
 case: (x1 =P x2) => [<-|Hx]; last by right; move=> [E]; case Hx.
by apply: (iffP (Hrec _)) => [<-|[E]].
Qed.

Canonical Structure seq_eqType := EqType eqseqP.

Lemma eqseqE : eqseq = set1. Proof. done. Qed.

Lemma eqseq_adds : forall x1 x2 s1 s2,
  (Adds x1 s1 == Adds x2 s2) = (x1 == x2) && (s1 == s2).
Proof. done. Qed.

(* Factories *)

Definition addsn n x := iter n (Adds x).
Definition seqn n x := addsn n x seq0.

Lemma size_addsn : forall n x s, size (addsn n x s) = n + size s.
Proof. by move=> n x p; elim: n => [|n Hrec] //=; rewrite Hrec. Qed.

Lemma size_seqn : forall n x, size (seqn n x) = n.
Proof. by move=> *; rewrite /seqn size_addsn addn0. Qed.

(* n-ary, dependently typed constructor. *)

Fixpoint nseq_type (n : nat) : Type :=
  if n is S n' then d -> nseq_type n' else seq.

Fixpoint nseq_rec (f : seq -> seq) (n : nat) {struct n} : nseq_type n :=
  match n as n' return (nseq_type n') with
  | O => f seq0
  | S n' => fun x => nseq_rec (fun s => f (Adds x s)) n'
  end.

Definition nseq : forall n : nat, nseq_type n := nseq_rec id.

(* Sequence catenation "cat".                                                *)

Fixpoint cat (s1 s2 : seq) {struct s1} : seq :=
  if s1 is Adds x s1' then Adds x (cat s1' s2) else s2.

Lemma cat0s : forall s, cat seq0 s = s. Proof. done. Qed.

Lemma cat1s : forall x s, cat (Seq x) s = Adds x s. Proof. done. Qed.

Lemma cat_adds : forall x s1 s2, cat (Adds x s1) s2 = Adds x (cat s1 s2).
Proof. done. Qed.

Lemma cat_seqn : forall n x s, cat (seqn n x) s = addsn n x s.
Proof. by elim=> //= *; congr Adds. Qed.

Lemma cats0 : forall s, cat s seq0 = s.
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma catA : forall s1 s2 s3, cat s1 (cat s2 s3) = cat (cat s1 s2) s3.
Proof. by move=> s1 s2 s3; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec. Qed.

Lemma size_cat : forall s1 s2, size (cat s1 s2) = size s1 + size s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec. Qed.

Lemma eqseq_cat : forall s1 s2 s3 s4, size s1 = size s2 ->
  (cat s1 s3 == cat s2 s4) = (s1 == s2) && (s3 == s4).
Proof.
move=> s1 s2 s3 s4 Hs12; elim: s1 s2 Hs12 => [|x1 s1 Hrec] [|x2 s2] //= [Hs12].
by rewrite !eqseq_adds -andbA Hrec.
Qed.

(* last, belast, add_last, and last induction. *)

Fixpoint add_last (s : seq) (z : d) {struct s} : seq :=
  if s is Adds x s' then Adds x (add_last s' z) else Seq z.

Lemma add_last_adds : forall x s z, add_last (Adds x s) z = Adds x (add_last s z).
Proof. done. Qed.

Lemma eqseq_add_last : forall s1 s2 x1 x2,
  (add_last s1 x1 == add_last s2 x2) = (s1 == s2) && (x1 == x2).
Proof.
move=> s1 s2 x1 x2; elim: s1 s2 => [|y1 s1 Hrec] [|y2 s2];
  rewrite /= ?eqseq_adds ?andbT ?andbF // ?Hrec 1?andbA // andbC;
  by [ case s2 | case s1 ].
Qed.

Lemma cats1 : forall s z, cat s (Seq z) = add_last s z.
Proof. by move=> s z; elim: s => //= [x s ->]. Qed.

Fixpoint last (x : d) (s : seq) {struct s} : d :=
  if s is Adds x' s' then last x' s' else x.

Fixpoint belast (x : d) (s : seq) {struct s} : seq :=
  if s is Adds x' s' then Adds x (belast x' s') else seq0.

Lemma lastI : forall x s, Adds x s = add_last (belast x s) (last x s).
Proof. by move=> x s; elim: s x => [|y s Hrec] x //=; rewrite Hrec. Qed.

Lemma last_adds : forall x y s, last x (Adds y s) = last y s.
Proof. done. Qed.

Lemma size_add_last : forall s x, size (add_last s x) = S (size s).
Proof. by move=> *; rewrite -cats1 size_cat addnC. Qed.

Lemma size_belast : forall x s, size (belast x s) = size s.
Proof. by move=> x s; elim: s x => [|y s Hrec] x //=; rewrite Hrec. Qed.

Lemma last_cat : forall x s1 s2, last x (cat s1 s2) = last (last x s1) s2.
Proof. by move=> x s1 s2; elim: s1 x => [|y s1 Hrec] x //=; rewrite Hrec. Qed.

Lemma last_add_last : forall x s z, last x (add_last s z) = z.
Proof. by move=> x s z; rewrite -cats1 last_cat. Qed.

Lemma belast_cat : forall x s1 s2,
  belast x (cat s1 s2) = cat (belast x s1) (belast (last x s1) s2).
Proof. by move=> x s1 s2; elim: s1 x => [|y s1 Hrec] x //=; rewrite Hrec. Qed.

Lemma belast_add_last : forall x s z, belast x (add_last s z) = Adds x s.
Proof. by move=> *; rewrite lastI -!cats1 belast_cat. Qed.

Lemma cat_add_last : forall x s1 s2, cat (add_last s1 x) s2 = cat s1 (Adds x s2).
Proof. by move=> *; rewrite -cats1 -catA. Qed.

Lemma add_last_cat : forall x s1 s2,
  add_last (cat s1 s2) x = cat s1 (add_last s2 x).
Proof. by move=> *; rewrite -!cats1 catA. Qed.

CoInductive last_spec : seq -> Type :=
  | LastSeq0 : last_spec seq0
  | LastAdd : forall (s : seq) (x : d), last_spec (add_last s x).

Lemma lastP : forall s, last_spec s.
Proof. move=> [|x s]; [ left | rewrite lastI; right ]. Qed.

Lemma last_ind : forall P,
  P seq0 -> (forall s x, P s -> P (add_last s x)) -> forall s, P s.
Proof.
move=> P Hseq0 Hlast s; rewrite -(cat0s s).
elim: s seq0 Hseq0 => [|x s2 Hrec] s1 Hs1; first by rewrite cats0.
by rewrite -cat_add_last; auto.
Qed.

(* Sequence indexing. *)

Fixpoint sub (s : seq) (n : nat) {struct n} : d :=
  if s is Adds x s' then if n is S n' then sub s' n' else x else x0.

Lemma sub0 : forall s, sub s 0 = head s. Proof. done. Qed.

Lemma sub_default : forall s n, size s <= n -> sub s n = x0.
Proof. by elim=> [|x s Hrec] [|n]; try exact (Hrec n). Qed.

Lemma sub_seq0 : forall n, sub seq0 n = x0.
Proof. by case. Qed.

Lemma sub_last : forall x s, sub (Adds x s) (size s) = last x s.
Proof. by move=> x s; elim: s x => [|y s Hrec] x /=. Qed.

Lemma sub_behead : forall s n, sub (behead s) n = sub s (S n).
Proof. by move=> [|x s] [|n]. Qed.

Lemma sub_cat : forall s1 s2 n,
 sub (cat s1 s2) n = if n < size s1 then sub s1 n else sub s2 (n - size s1).
Proof.
by move=> s1 s2 n; elim: s1 n => [|x s1 Hrec] [|n]; try exact (Hrec n).
Qed.

Lemma sub_add_last : forall s x n,
 sub (add_last s x) n =
   if n < size s then sub s n else if n == size s then x else x0.
Proof.
move=> s x n; rewrite -cats1 sub_cat eqn_leq andbC /= ltnNge -(eqn_sub0 n) /=.
by case (leq (size s) n); first by case: (n - (size s)) => [|[|m]].
Qed.

(* mem, find, count, has, all, and index; mem is a coercion to set. *)

Fixpoint mem (s : seq) : set d :=
  if s is Adds x s' then setU1 x (mem s') else set0.

Coercion mem : seq >-> set.

Lemma mem_adds : forall x s, Adds x s =1 setU1 x s. Proof. done. Qed.

Lemma mem_seq1 : forall x, Seq x =1 set1 x.
Proof. by move=> x1 y; rewrite /= /setU1 orbF. Qed.

Lemma mem_seq2 : forall x1 x2, Seq x1 x2 =1 set2 x1 x2.
Proof. by move=> x1 x2 y; rewrite /= /setU1 orbF. Qed.

Lemma mem_seq3 : forall x1 x2 x3, Seq x1 x2 x3 =1 set3 x1 x2 x3.
Proof. by move=> x1 x2 x3 y; rewrite /= /setU1 orbF. Qed.

Lemma mem_seq4 : forall x1 x2 x3 x4, Seq x1 x2 x3 x4 =1 set4 x1 x2 x3 x4.
Proof. by move=> x1 x2 x3 x4 y; rewrite /= /setU1 orbF. Qed.

Lemma mem_cat : forall s1 s2, cat s1 s2 =1 setU s1 s2.
Proof.
move=> s1 s2 y; elim: s1 => [|x s1 Hrec] //=.
by rewrite /setU /setU1 -orbA Hrec.
Qed.

Lemma mem_add_last : forall s x, add_last s x =1 Adds x s.
Proof. by move=> s x y; rewrite -cats1 mem_cat /setU mem_seq1 orbC. Qed.

Lemma mem_last : forall x s, Adds x s (last x s).
Proof. by move=> *; rewrite lastI mem_add_last /= setU11. Qed.

Lemma mem_lastU : forall x (s : seq), setU1 x s (last x s).
Proof. exact mem_last. Qed.

Lemma mem_behead : forall s y, behead s y -> s y.
Proof. move=> [|x s] //; apply: setU1r. Qed.

Lemma mem_belast : forall x s y, belast x s y -> Adds x s y.
Proof. by move=> *; rewrite lastI mem_add_last /= setU1r. Qed.

Lemma mem_sub : forall s n, n < size s -> s (sub s n).
Proof.
by elim=> [|x s Hrec] // [|n] /=; [rewrite setU11 | move/Hrec; apply: setU1r].
Qed.

Section SeqFind.

Variable a : set d.

Fixpoint find (s : seq) : nat :=
  if s is Adds x s' then if a x then 0 else S (find s') else 0.

Fixpoint filter (s : seq) : seq :=
  if s is Adds x s' then (if a x then Adds x else id) (filter s') else seq0.

Fixpoint count (s : seq) : nat :=
  if s is Adds x s' then addn (a x) (count s') else 0.

Fixpoint has (s : seq) : bool :=
  if s is Adds x s' then a x || has s' else false.

Fixpoint all (s : seq) : bool :=
  if s is Adds x s' then a x && all s' else true.

Lemma count_filter : forall s, count s = size (filter s).
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec; case (a x). Qed.

Lemma has_count : forall s, has s = (0 < count s).
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec; case (a x). Qed.

Lemma count_size : forall s, count s <= size s.
Proof. by elim=> [|x s Hrec] //=; case (a x); last by apply ltnW. Qed.

Lemma all_count : forall s, all s = (count s == size s).
Proof.
elim=> [|x s Hrec] //=; case: (a x) => [|] //=.
by rewrite add0n eqn_leq andbC ltnNge count_size.
Qed.

Lemma has_filter : forall s, has s = if filter s is Seq0 then false else true.
Proof. by move=> s; rewrite has_count count_filter; case (filter s). Qed.

Lemma all_filterP : forall s, reflect (filter s = s) (all s).
Proof.
move=> s; apply introP.
  by elim: s => [|x s Hrec] //=; case/andP=> [Ha Hs]; rewrite Ha Hrec.
by rewrite all_count count_filter; move=> H H'; rewrite H' set11 in H.
Qed.

Lemma has_find : forall s, has s = (find s < size s).
Proof. by elim=> [|x s Hrec] //=; case (a x); rewrite ?leqnn. Qed.

Lemma find_size : forall s, find s <= size s.
Proof. by elim=> [|x s Hrec] //=; case (a x). Qed.

Lemma find_cat : forall s1 s2,
  find (cat s1 s2) = if has s1 then find s1 else size s1 + find s2.
Proof.
move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; case: (a x) => [|] //.
by rewrite Hrec (fun_if S).
Qed.

Lemma has_seq0 : has seq0 = false. Proof. done. Qed.

Lemma has_seq1 : forall x, has (Seq x) = a x.
Proof. by move=> *; rewrite /= orbF. Qed.

Lemma has_seqb : forall (b : bool) x, has (seqn b x) = b && a x.
Proof. by case=> // *; rewrite /= orbF. Qed.

Lemma all_seq0 : all seq0 = true. Proof. done. Qed.

Lemma all_seq1 : forall x, all (Seq x) = a x.
Proof. by move=> *; rewrite /= andbT. Qed.

Lemma sub_find : forall s, has s -> a (sub s (find s)).
Proof. by elim=> [|x s Hrec] //=; case Hx: (a x). Qed.

Lemma before_find : forall s i, i < find s -> a (sub s i) = false.
Proof.
move=> s i; elim: s i => [|x s Hrec] //=; case Hx: (a x) => [|] // [|i] //.
exact (Hrec i).
Qed.

Lemma hasP : forall s : seq, reflect (exists2 x, s x & a x) (has s).
Proof.
elim=> [|x s Hrec] /=; first by right; move=> [x Hx _].
case Hax: (a x); first by left; exists x; first by rewrite /= setU11.
apply: (iffP Hrec) => [] [y Hy Hay]; exists y => //; first exact: setU1r.
by case: (setU1P Hy) => [Dx|Hx] //; rewrite Dx Hay in Hax.
Qed.

Lemma hasPn : forall s : seq, reflect (forall x, s x -> ~~ a x) (~~ has s).
Proof.
move=> s; apply: (iffP idP) => [Hs x Hx|Hs].
  by apply/negP => Hax; case/hasP: Hs; exists x.
by apply/hasP=> [] [x Hx Hax]; case (negP (Hs _ Hx)).
Qed.

Lemma allP : forall s : seq, reflect (forall x, s x -> a x) (all s).
Proof.
elim=> [|x s Hrec]; first by left.
rewrite /= andbC; case: Hrec => Hrec /=.
  apply: (iffP idP) => [Hx y|H]; last by apply H; apply setU11.
  by case/setU1P=> [<-|Hy]; auto.
by right; move=> H; case Hrec => y Hy; apply H; apply setU1r.
Qed.

Lemma allPn : forall s : seq, reflect (exists2 x, s x & ~~ a x) (~~ all s).
Proof.
elim=> [|x s Hrec]; first by right; move=> [x Hx _].
rewrite /= andbC negb_andb; case: Hrec => [Hrec|Hrec]; simpl.
  by left; case: Hrec => y Hy Hay; exists y; first by apply setU1r.
case Hax: (a x); constructor; last by exists x; rewrite ?Hax ?setU11.
move=> [y Hy Hay]; case Hrec; exists y; last done.
by case/setU1P: Hy Hay => [<-|Hy]; first by rewrite Hax.
Qed.

Lemma filter_cat : forall s1 s2, filter (cat s1 s2) = cat (filter s1) (filter s2).
Proof.
by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec; case (a x).
Qed.

Lemma filter_add_last : forall s x,
  filter (add_last s x) = if a x then add_last (filter s) x else filter s.
Proof.
by move=> s x; rewrite -!cats1 filter_cat /=; case (a x); rewrite /= ?cats0.
Qed.

Lemma mem_filter : forall s, filter s =1 setI a s.
Proof.
move=> s y; rewrite /setI andbC; elim: s => [|x s Hrec] //=.
rewrite if_arg /id (fun_if (fun s' : seq => s' y)) /= /setU1 Hrec.
by case: (x =P y) => [<-|_]; case (a x); rewrite /= ?andbF.
Qed.

Lemma count_cat : forall s1 s2, count (cat s1 s2) = count s1 + count s2.
Proof. by move=> *; rewrite !count_filter filter_cat size_cat. Qed.

Lemma has_cat : forall s1 s2 : seq, has (cat s1 s2) = has s1 || has s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec orbA. Qed.

Lemma has_add_last : forall s x, has (add_last s x) = a x || has s.
Proof. by move=> *; rewrite -cats1 has_cat has_seq1 orbC. Qed.

Lemma all_cat : forall s1 s2, all (cat s1 s2) = all s1 && all s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec andbA. Qed.

Lemma all_add_last : forall s x, all (add_last s x) = a x && all s.
Proof. by move=> *; rewrite -cats1 all_cat all_seq1 andbC. Qed.

End SeqFind.

Lemma eq_find : forall a1 a2, a1 =1 a2 -> find a1 =1 find a2.
Proof. by move=> a1 a2 Ea; elim=> [|x s Hrec] //=; rewrite Ea Hrec. Qed.

Lemma eq_filter : forall a1 a2, a1 =1 a2 -> filter a1 =1 filter a2.
Proof. by move=> a1 a2 Ea; elim=> [|x s Hrec] //=; rewrite Ea Hrec. Qed.

Lemma eq_count : forall a1 a2, a1 =1 a2 -> count a1 =1 count a2.
Proof. by move=> a1 a2 Ea s; rewrite !count_filter (eq_filter Ea). Qed.

Lemma eq_has : forall a1 a2, a1 =1 a2 -> has a1 =1 has a2.
Proof. by move=> a1 a2 Ea s; rewrite !has_count (eq_count Ea). Qed.

Lemma eq_has_r : forall s1 s2 : seq, s1 =1 s2 -> forall a, has a s1 = has a s2.
Proof.
move=> s1 s2 Es12 a; apply/(hasP a s1)/(hasP a s2) => [] [x Hx Hax];
 by exists x; rewrite // ?Es12 // -Es12.
Qed.

Lemma eq_all : forall a1 a2, a1 =1 a2 -> all a1 =1 all a2.
Proof. by move=> a1 a2 Ea s; rewrite !all_count (eq_count Ea). Qed.

Lemma eq_all_r : forall s1 s2 : seq,  s1 =1 s2 -> forall a, all a s1 = all a s2.
Proof.
by move=> s1 s2 Es12 a; apply/(allP a s1)/(allP a s2) => Hs x Hx;
  apply Hs; rewrite Es12 in Hx *.
Qed.

Lemma filter_set0 : forall s, filter set0 s = seq0. Proof. by elim. Qed.

Lemma filter_setA : forall s, filter d s = s.
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma filter_setI : forall a1 a2 s,
  filter (setI a1 a2) s = filter a1 (filter a2 s).
Proof.
move=> a1 a2; elim=> [|x s Hrec] //=; rewrite /= {1}/setI andbC Hrec.
by case: (a2 x) => [|] //=; case (a1 x).
Qed.

Lemma count_set0 : forall s, count set0 s = 0.
Proof. by move=> s; rewrite count_filter filter_set0. Qed.

Lemma count_setA : forall s, count d s = size s.
Proof. by move=> s; rewrite count_filter filter_setA. Qed.

Lemma count_setUI : forall a1 a2 s,
 count (setU a1 a2) s + count (setI a1 a2) s = count a1 s + count a2 s.
Proof.
move=> a1 a2; elim=> [|x s Hrec] //=; rewrite /= addnCA -addnA Hrec addnA addnC.
by rewrite -!addnA /setU /setI; do 2 nat_congr; case (a1 x); case (a2 x).
Qed.

Lemma count_setC : forall a s, count a s + count (setC a) s = size s.
Proof.
move=> a; elim=> [|x s Hrec] //=; rewrite -!addnA (addnCA (count a s)) Hrec /=.
by rewrite /setC; case (a x).
Qed.

Lemma has_set0 : forall s, has set0 s = false.
Proof. by move=> s; rewrite has_count count_set0. Qed.

Lemma has_setA : forall s, has d s = (0 < size s).
Proof. by move=> s; rewrite has_count count_setA. Qed.

Lemma has_setC : forall a s, has (setC a) s = ~~ all a s.
Proof. move=> a s; exact (sameP (hasP (setC a) _) (allPn _ _)). Qed.

Lemma has_setU : forall a1 a2 s, has (setU a1 a2) s = has a1 s || has a2 s.
Proof.
by move=> a1 a2; elim=> //= [x s ->]; rewrite /setU -!orbA; do !bool_congr.
Qed.

Lemma all_set0 : forall s, all set0 s = (size s == 0).
Proof. by move=> *; rewrite all_count count_set0 eq_sym. Qed.

Lemma all_setA : forall s, all d s = true.
Proof. by move=> *; rewrite all_count count_setA set11. Qed.

Lemma all_setC : forall a s, all (setC a) s = ~~ has a s.
Proof. move=> a s; exact (sameP (allP (setC a) _) (hasPn _ _)). Qed.

Lemma all_setI : forall a1 a2 s, all (setI a1 a2) s = all a1 s && all a2 s.
Proof.
move=> a1 a2 s; apply: can_inj negb negbK _ _ _.
rewrite negb_andb -!has_setC -has_setU; apply: eq_has => x.
by rewrite /setC /setI negb_andb.
Qed.

Lemma has_sym : forall s1 s2 : seq, has s1 s2 = has s2 s1.
Proof. by move=> s1 s2; apply/(hasP s1 s2)/(hasP s2 s1) => [] [x]; exists x. Qed.

Lemma has_set1 : forall x s, has (set1 x) s = s x.
Proof. by move=> x *; rewrite -(eq_has (mem_seq1 x)) has_sym /= orbF. Qed.

(* Duplicate-freenes. *)

Fixpoint uniq (s : seq) : bool :=
  if s is Adds x s' then ~~ s' x && uniq s' else true.

Lemma uniq_adds : forall x s, uniq (Adds x s) = ~~ s x && uniq s.
Proof. done. Qed.

Lemma uniq_cat : forall s1 s2,
   uniq (cat s1 s2) = (and3b (uniq s1) (~~ has s1 s2) (uniq s2)).
Proof.
move=> s1 s2; elim: s1 => [|x s1 Hrec]; first by rewrite /= has_set0.
by rewrite has_sym /= mem_cat /setU !negb_orb has_sym Hrec -!andbA; do !bool_congr.
Qed.

Lemma uniq_catC : forall s1 s2, uniq (cat s1 s2) = uniq (cat s2 s1).
Proof. by move=> *; rewrite !uniq_cat has_sym andbCA andbA andbC. Qed.

Lemma uniq_catCA : forall s1 s2 s3,
  uniq (cat s1 (cat s2 s3)) = uniq (cat s2 (cat s1 s3)).
Proof.
move=> s1 s2 s3.
by rewrite !catA -!(uniq_catC s3) !(uniq_cat s3) uniq_catC !has_cat orbC.
Qed.

Lemma uniq_add_last : forall s x, uniq (add_last s x) = ~~ s x && uniq s.
Proof. by move=> *; rewrite -cats1 uniq_catC. Qed.

Lemma uniq_filter : forall s a, uniq s -> uniq (filter a s).
Proof.
move=> s a; elim: s => [|x s Hrec] //=; case/andP=> [Hx Hs]; case (a x); auto.
by rewrite /= mem_filter /setI (negbET Hx) andbF; auto.
Qed.

Lemma count_set1_uniq : forall s x, uniq s -> count (set1 x) s = s x.
Proof.
move=> s x; elim: s => //= [y s IHs]; case/andP; move/negbET=> Hy Us.
by rewrite {}IHs {Us}// /setU1 eq_sym; case: eqP => // <-; rewrite Hy.
Qed.

(* Removing duplicates *)

Fixpoint undup (s : seq) : seq :=
  if s is Adds x s' then
    if s' x then undup s' else Adds x (undup s')
  else seq0.

Lemma size_undup : forall s, size (undup s) <= size s.
Proof. elim=> //= [x s IHs]; case: (s x) => //=; exact: ltnW. Qed.

Lemma mem_undup : forall s, undup s =1 s.
Proof.
move=> s x; elim: s => //= [y s IHs].
by case Hy: (s y); rewrite /= /setU1 IHs //; case: eqP => // <-.
Qed.

Lemma uniq_undup : forall s, uniq (undup s).
Proof.
by elim=> //= [x s IHs]; case Hx: (s x); rewrite //= mem_undup Hx.
Qed.

Lemma undup_uniq : forall s, uniq s -> undup s = s.
Proof. by elim=> //= [x s IHs]; case/andP; move/negbET->; move/IHs->. Qed.

Lemma ltn_size_undup : forall s, (size (undup s) < size s) = ~~ uniq s.
Proof.
by elim=> //= [x s IHs]; case Hx: (s x); rewrite //= ltnS size_undup.
Qed. 

(* Lookup *)

Definition index x := find (set1 x).

Lemma index_size : forall x s, index x s <= size s.
Proof. by move=> *; rewrite /index find_size. Qed.

Lemma index_mem : forall x s, (index x s < size s) = s x.
Proof. by move=> *; rewrite -has_set1 has_find. Qed.

Lemma sub_index : forall x (s : seq), s x -> sub s (index x s) = x.
Proof. by move=> *; apply: (esym (eqP (sub_find _))); rewrite has_set1. Qed.

Lemma index_cat : forall x s1 s2,
 index x (cat s1 s2) = if s1 x then index x s1 else size s1 + index x s2.
Proof. by move=> x s1 s2; rewrite /index find_cat has_set1. Qed.

Lemma index_uniq : forall i s, i < size s -> uniq s -> index (sub s i) s = i.
Proof.
move=> i s; simpl; elim: s i => [|x s Hrec] //= [|i]; rewrite /= ?set11 // ltnS.
move=> Hi; case/andP=> [Hx Hs]; rewrite (Hrec i Hi Hs).
by case: (sub s i =P x) Hx => [<-|_]; first by rewrite mem_sub.
Qed.

Lemma index_head : forall x s, index x (Adds x s) = 0.
Proof. by move=> *; rewrite /= set11. Qed.

Lemma index_last : forall x s,
  uniq (Adds x s) -> index (last x s) (Adds x s) = size s.
Proof. by move=> *; rewrite -sub_last index_uniq //= leqnn. Qed.

(* Surgery: drop, take, rot, rotr.                                              *)

Fixpoint drop (n : nat) (s : seq) {struct s} : seq :=
  match s, n with
  | Adds _ s', S n' => drop n' s'
  | _, _ => s
  end.

Lemma drop_behead : drop n0 =1 iter n0 behead.
Proof. by elim: n0 => [|n Hrec] [|x s] //; rewrite -iter_f -Hrec. Qed.

Lemma drop0 : forall s, drop 0 s = s. Proof. by case. Qed.

Lemma drop1 : drop 1 =1 behead. Proof. by move=> [|x [|y s]]. Qed.

Lemma drop_oversize : forall n s, size s <= n -> drop n s = seq0.
Proof. by elim=> [|n Hrec] [|x s]; try exact (Hrec s). Qed.

Lemma drop_size : forall s, drop (size s) s = seq0.
Proof. by move=> s; rewrite drop_oversize // leqnn. Qed.

Lemma drop_adds : forall x s,
  drop n0 (Adds x s) = if n0 is S n then drop n s else Adds x s.
Proof. done. Qed.

Lemma size_drop : forall s, size (drop n0 s) = size s - n0.
Proof. by move=> s; elim: s n0 => [|x s Hrec] [|n]; try exact (Hrec n). Qed.

Lemma drop_cat : forall s1 s2,
 drop n0 (cat s1 s2) =
   if n0 < size s1 then cat (drop n0 s1) s2 else drop (n0 - size s1) s2.
Proof.
by move=> s1 s2; elim: s1 n0 => [|x s1 Hrec] [|n]; try exact (Hrec n).
Qed.

Lemma drop_size_cat : forall s1 s2, drop (size s1) (cat s1 s2) = s2.
Proof. by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite drop0. Qed.

Fixpoint take (n : nat) (s : seq) {struct s} : seq :=
  match s, n with
  | Adds x s', S n' => Adds x (take n' s')
  | _, _ => seq0
  end.

Lemma take0 : forall s, take 0 s = seq0. Proof. by case. Qed.

Lemma take_oversize : forall n s, size s <= n -> take n s = s.
Proof. by elim=> [|n Hrec] [|x s] Hsn; try (congr Adds; apply: Hrec). Qed.

Lemma take_size : forall s, take (size s) s = s.
Proof. by move=> s; rewrite take_oversize // leqnn. Qed.

Lemma take_adds : forall x s,
  take n0 (Adds x s) = if n0 is S n then Adds x (take n s) else seq0.
Proof. done. Qed.

Lemma drop_add_last : forall s, n0 <= size s ->
  forall x, drop n0 (add_last s x) = add_last (drop n0 s) x.
Proof. by move=> s; elim: s n0 => [|y s Hrec] [|n]; try exact (Hrec n). Qed.

Lemma cat_take_drop : forall s, cat (take n0 s) (drop n0 s) = s.
Proof.
by move=> s; elim: s n0 => [|x s Hrec] [|n]; try exact (congr1 _ (Hrec n)).
Qed.

Lemma size_takel : forall s, n0 <= size s -> size (take n0 s) = n0.
Proof.
move=> s Hn0; apply: (addn_injr (etrans _ (esym (subnKl Hn0)))).
by rewrite -size_drop -size_cat cat_take_drop.
Qed.

Lemma size_take : forall s,
  size (take n0 s) = if n0 < size s then n0 else size s.
Proof.
move=> s; case: (ltnP n0 (size s));
 last by move=> *; rewrite take_oversize.
by move=> *; apply size_takel; apply ltnW.
Qed.

Lemma take_cat : forall s1 s2,
 take n0 (cat s1 s2) =
   if n0 < size s1 then take n0 s1 else cat s1 (take (n0 - size s1) s2).
Proof.
move=> s1 s2; elim: s1 n0 => [|x s1 Hrec] [|n] //=.
by rewrite ltnS subSS -(fun_if (Adds x)) -Hrec.
Qed.

Lemma take_size_cat : forall s1 s2, take (size s1) (cat s1 s2) = s1.
Proof.
by move=> s1 s2; elim: s1 => [|x s1 Hrec]; [ case s2 | exact (congr1 _ Hrec) ].
Qed.

Lemma takel_cat : forall s1, n0 <= size s1 ->
  forall s2, take n0 (cat s1 s2) = take n0 s1.
Proof.
move=> s1 Hn0 s2; rewrite take_cat ltn_neqAle Hn0 andbT.
case: (n0 =P size s1) => [Dn0|_] //.
by rewrite Dn0 subnn take0 cats0 take_size.
Qed.

Lemma mem_take : forall s, sub_set (take n0 s) s.
Proof. by move=> s x Hx; rewrite -(cat_take_drop s) mem_cat /setU Hx. Qed.

Lemma mem_drop : forall s, sub_set (drop n0 s) s.
Proof. by move=> s x Hx; rewrite -(cat_take_drop s) mem_cat /setU Hx orbT. Qed.

Lemma sub_drop : forall s i, sub (drop n0 s) i = sub s (n0 + i).
Proof.
move=> s i; case: (ltnP n0 (size s)) => [Hn|Hn].
  rewrite -{2}[s]cat_take_drop sub_cat size_take Hn /=.
  by rewrite ltnNge leq_addr addKn.
rewrite !sub_default //; first by apply: (leq_trans Hn); apply: leq_addr.
by rewrite -eqn_sub0 in Hn; rewrite size_drop (eqP Hn) leq0n.
Qed.

Lemma sub_take : forall i, i < n0 -> forall s, sub (take n0 s) i = sub s i.
Proof.
move=> i Hi s; case Hn: (n0  < size s).
  by rewrite -{2}[s]cat_take_drop sub_cat size_take Hn /= Hi.
by rewrite -{1}[s]cats0 take_cat Hn /= cats0.
Qed.

(* drop_sub and take_sub below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the sub default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_sub : forall n s, n < size s ->
  drop n s = Adds (sub s n) (drop (S n) s).
Proof.
by move=> n s; elim: s n => [|x s Hrec] [|n] Hn //=; rewrite ?drop0 1?Hrec.
Qed.

Lemma take_sub : forall n s, n < size s ->
  take (S n) s = add_last (take n s) (sub s n).
Proof.
by move=> n s; elim: s n => [|x s Hrec] //= [|n] Hn /=; rewrite ?take0 -?Hrec.
Qed.

Lemma eq_from_sub : forall s1 s2, size s1 = size s2 ->
  (forall i, i < size s1 -> sub s1 i = sub s2 i) -> s1 = s2.
Proof.
move=> s1 s2 Hs12 Es12; rewrite -{1}[s2]take_size -{1}[s1]take_size -Hs12.
elim: {-2}(size s1) (leqnn (size s1)) => [|n Hrec] Hn; first by rewrite !take0.
by rewrite (take_sub Hn) (Es12 _ Hn) (Hrec (ltnW Hn)) -take_sub // -Hs12.
Qed.

Definition rot n s := cat (drop n s) (take n s).

Lemma rot0 : forall s, rot 0 s = s.
Proof. by move=> *; rewrite /rot drop0 take0 cats0. Qed.

Lemma size_rot : forall s, size (rot n0 s) = size s.
Proof. by move=> s; rewrite -{2}[s]cat_take_drop /rot !size_cat addnC. Qed.

Lemma rot_oversize : forall n s, size s <= n -> rot n s = s.
Proof. by move=> n s Hn; rewrite /rot (take_oversize Hn) (drop_oversize Hn). Qed.

Lemma rot_size : forall s, rot (size s) s = s.
Proof. exact (fun s => rot_oversize (leqnn _)). Qed.

Lemma mem_rot : forall s, rot n0 s =1 s.
Proof. by move=> s x; rewrite -{2}[s]cat_take_drop /rot !mem_cat /setU orbC. Qed.

Lemma has_rot : forall s a, has a (rot n0 s) = has a s.
Proof. move=> *; apply: eq_has_r; apply: mem_rot. Qed.

Lemma uniq_rot : forall s, uniq (rot n0 s) = uniq s.
Proof. by move=> *; rewrite /rot uniq_catC cat_take_drop. Qed.

Lemma rot_size_cat : forall s1 s2, rot (size s1) (cat s1 s2) = cat s2 s1.
Proof. by move=> *; rewrite /rot take_size_cat drop_size_cat. Qed.

Definition rotr n s := rot (size s - n) s.

Lemma rotK : cancel (rot n0) (rotr n0).
Proof.
by move=> s; rewrite /rotr size_rot -size_drop {2}/rot rot_size_cat cat_take_drop.
Qed.

Lemma rot_inj : injective (rot n0). Proof. exact (can_inj rotK). Qed.

Lemma eqseq_rot : forall s1 s2, (rot n0 s1 == rot n0 s2) = (s1 == s2).
Proof. apply: inj_eq; exact rot_inj. Qed.

CoInductive rot_to_spec (s : seq) (x : d) : Type :=
  RotToSpec i s' (_ : rot i s = Adds x s').

Lemma rot_to : forall (s : seq) x, s x -> rot_to_spec s x.
Proof.
move=> s x Hx; set i := index x s; exists i (cat (drop (S i) s) (take i s)).
rewrite {}/i /rot -cat_adds; congr cat; elim: s Hx => [|y s Hrec] //=.
by rewrite /setU1 eq_sym; case: (x =P y) => [<-|_]; [ rewrite drop0 | auto ].
Qed.

Lemma rot1_adds : forall x s, rot 1 (Adds x s) = add_last s x.
Proof. by move=> *; rewrite /rot /= take0 drop0 -cats1. Qed.

(* (efficient) reversal *)

Fixpoint catrev (s2 s1 : seq) {struct s1} : seq :=
  if s1 is Adds x s1' then catrev (Adds x s2) s1' else s2.

Definition rev s := nosimpl catrev seq0 s.

Lemma rev_add_last : forall s x, rev (add_last s x) = Adds x (rev s).
Proof. by move=> s x; rewrite /rev -cats1 /=; elim: s {-2}seq0 => /=. Qed.

Lemma rev_adds :
 forall (x : d) s, rev (Adds x s) = add_last (rev s) x.
Proof.
move=> x; elim/last_ind=> [|s y Hrec] //.
by rewrite rev_add_last /= -Hrec -rev_add_last.
Qed.

Lemma size_rev : forall s, size (rev s) = size s.
Proof. by elim=> [|x s Hrec] //; rewrite rev_adds size_add_last Hrec. Qed.

Lemma rev_cat : forall s1 s2, rev (cat s1 s2) = cat (rev s2) (rev s1).
Proof.
move=> s1 s2; elim: s1 => [|x s1 Hrec] /=; first by rewrite cats0.
by rewrite !rev_adds Hrec -!cats1 catA.
Qed.

Lemma revK : involutive rev.
Proof. by elim=> [|x s Hrec] //=; rewrite rev_adds rev_add_last Hrec. Qed.

Lemma mem_rev : forall s : seq, rev s =1 s.
Proof.
move=> s y; elim: s => [|x s Hrec] //.
by rewrite rev_adds /= mem_add_last /= /setU1 Hrec.
Qed.

Lemma uniq_rev : forall s, uniq (rev s) = uniq s.
Proof.
elim=> [|x s Hrec] //.
by rewrite rev_adds -cats1 uniq_cat /= andbT andbC mem_rev orbF Hrec.
Qed.

Lemma sub_rev : forall n s, n < size s -> sub (rev s) n = sub s (size s - S n).
Proof.
move=> n s; elim/last_ind: s n => [|s x Hrec] n //.
rewrite rev_add_last size_add_last ltnS subSS -cats1 sub_cat /=.
case: n => [|n] Hn; first by rewrite subn0 ltnn subnn.
rewrite -{2}[size s](subnKl Hn) addSnnS leq_addl /=; auto.
Qed.

End Sequences.

Notation seq0 := (Seq0 _).
Notation adds := (@Adds _) (only parsing).

Notation "'Seq' x1" := (Adds x1 seq0) : seq_scope.

Notation "'Seq' x1 x2 .. y & s" := (Adds x1 (Adds x2 .. (Adds y s) .. ))
                                : seq_scope.

Notation "'Seq' x1 x2 .. y" := (Adds x1 (Adds x2 .. (Seq y) .. )) : seq_scope.

Prenex Implicits size head behead last add_last belast.
Prenex Implicits cat take drop rev rot rotr.
Prenex Implicits find count uniq undup index sub all has filter.

Implicit Arguments eqseqP [d x y].
Implicit Arguments all_filterP [d a s].
Implicit Arguments hasP [d a s].
Implicit Arguments hasPn [d a s].
Implicit Arguments allP [d a s].
Implicit Arguments allPn [d a s].
Prenex Implicits eqseqP all_filterP hasP hasPn allP allPn.

Section SeqSubTheory.

Variables (d : eqType) (a : set d) (s : seq d).

Lemma subP : forall x x0, reflect (exists2 i, i < size s & sub x0 s i = x) (s x).
Proof.
move=> x x0; apply: (iffP idP) => [|[n Hn <-]]; last by apply mem_sub.
by exists (index x s); [ rewrite index_mem | apply sub_index ].
Qed.

Lemma has_subP : forall x0,
  reflect (exists2 i, i < size s & a (sub x0 s i)) (has a s).
Proof.
move=> x0; apply: (iffP hasP) => [[x Hx Hax]|[i Hi Hai]].
  by case/(subP _ x0): Hx Hax => [i Hi <-]; exists i.
by exists (sub x0 s i); first by apply mem_sub.
Qed.

Lemma all_subP : forall x0,
  reflect (forall i, i < size s -> a (sub x0 s i)) (all a s).
Proof.
move=> x0; apply: (iffP allP) => [Hs i Hi|Hs x].
  by apply Hs; apply mem_sub.
case/(subP _ x0) => [i Hi <-]; auto.
Qed.

Lemma set_sub_default : forall y0 x0 n, n < size s -> sub x0 s n = sub y0 s n.
Proof. by move=> y0 x0; elim: s => [|y s' Hrec] [|n] /=; auto. Qed.

Lemma headI : forall x, add_last s x = Adds (head x s) (behead (add_last s x)).
Proof. by case s. Qed.

End SeqSubTheory.

Implicit Arguments subP [d s x].
Implicit Arguments has_subP [d a s].
Implicit Arguments all_subP [d a s].
Prenex Implicits subP has_subP all_subP.

Definition bitseq := seq bool_eqType.

Definition natseq := seq nat_eqType.

(* Incrementing the ith nat in a natseq, padding with 0's if needed. This      *)
(* allows us to use natseqs as bags of nats.                                   *)

Fixpoint incr_sub (v : natseq) (i : nat) {struct i} : natseq :=
  if v is Adds n v' then
    if i is S i' then Adds n (incr_sub v' i') else Adds (S n) v'
  else
    addsn i 0 (Seq 1).

Lemma sub_incr_sub : forall v i j, sub 0 (incr_sub v i) j = (i == j) + sub 0 v j.
Proof.
elim=> [|n v Hrec] [|i] [|j] //=; rewrite ?eqSS ?addn0 //; try by case j.
elim: i j => [|i Hrec] [|j] //=; rewrite ?eqSS //; by case j.
Qed.

Lemma size_incr_sub : forall v i,
  size (incr_sub v i) = if i < size v then size v else S i.
Proof.
elim=> [|n v Hrec] [|i] //=; first by rewrite size_addsn /= addn1.
rewrite Hrec; exact: fun_if.
Qed.

Section UniqPerm.

Variable d : eqType.

Lemma uniq_leq_size : forall s1 s2 : seq d,
  uniq s1 -> sub_set s1 s2 -> size s1 <= size s2.
Proof.
elim=> [|x s1 Hrec] /= s2; [ by case s2 | move/andP=> [Hx Hs1] Hs12 ].
case: (@rot_to d s2 x); first by apply: Hs12; apply: setU11.
move=> i s2' Ds2'; rewrite -(size_rot i s2) (Ds2'); apply: Hrec => // [y Hy].
move: (Hs12 _ (setU1r _ Hy)); rewrite -(mem_rot i) Ds2'; case/setU1P=> //.
by move=> Dx; rewrite Dx Hy in Hx.
Qed.

Lemma leq_size_uniq : forall s1 s2 : seq d,
  uniq s1 -> sub_set s1 s2 -> size s2 <= size s1 -> uniq s2.
Proof.
elim=> [|x s1 Hrec] s2 Hs1 Hs12; first by case s2.
case: (@rot_to d s2 x); [ by apply: Hs12; apply: setU11 | move=> i s2' Ds2' ].
  rewrite -(size_rot i) -(uniq_rot i) (Ds2') /=; case Hs2': (s2' x).
  rewrite ltnNge; case/negP; apply: (uniq_leq_size Hs1) => [y Hy].
  by move: (Hs12 _ Hy); rewrite -(mem_rot i) Ds2'; case/setU1P=> // [<-].
simpl in Hs1; move/andP: Hs1 => [Hx Hs1]; apply: Hrec => // [y Hy].
move: (Hs12 _ (setU1r _ Hy)); rewrite -(mem_rot i) Ds2'; case/setU1P=> //.
by move=> Dx; rewrite Dx Hy in Hx.
Qed.

Lemma uniq_size_uniq : forall s1 s2 : seq d,
  uniq s1 -> s1 =1 s2 -> uniq s2 = (size s2 == size s1).
Proof.
move=> s1 Hs1 s2 Es12.
rewrite eqn_leq andbC uniq_leq_size //=; last by move=> y; rewrite Es12.
apply/idP/idP => [Hs2|]; first by apply: uniq_leq_size => // y; rewrite Es12.
by apply: leq_size_uniq => // y; rewrite Es12.
Qed.

Lemma leq_size_perm : forall s1 s2 : seq d,
  uniq s1 -> sub_set s1 s2 -> size s2 <= size s1 ->
    s1 =1 s2 /\ size s1 = size s2.
Proof.
move=> s1 s2 Us1 Hs1 Hs12; have Us2: uniq s2 by exact: leq_size_uniq Hs12.
suff: s1 =1 s2 by split; last by apply/eqP; rewrite -uniq_size_uniq.
move=> x; apply/idP/idP; auto=> Hxs2; apply/idPn=> Hxs1.
suff: size (Adds x s1) <= size s2 by rewrite /= ltnNge Hs12.
apply: uniq_leq_size; first by rewrite /= Hxs1.
move=> y /=; case/setU1P=> [<-|Hys1]; auto.
Qed.

Lemma uniq_perm : forall s1 s2 : seq d,
  s1 =1 s2 -> size s1 = size s2 -> uniq s1 = uniq s2.
Proof.
move=> s1 s2 Es12 Hs12; apply/idP/idP => Us;
  by rewrite (uniq_size_uniq Us) ?Hs12 ?set11.
Qed.

End UniqPerm.

Section RotrLemmas.

Variables (n0 : nat) (d : eqType).

Lemma size_rotr : forall s : seq d, size (rotr n0 s) = size s.
Proof. by move=> *; rewrite /rotr size_rot. Qed.

Lemma mem_rotr : forall s : seq d, rotr n0 s =1 s.
Proof. by move=> s x; rewrite /rotr mem_rot. Qed.

Lemma rotr_size_cat : forall s1 s2 : seq d, rotr (size s2) (cat s1 s2) = cat s2 s1.
Proof. by move=> *; rewrite /rotr size_cat addnK rot_size_cat. Qed.

Lemma rotr1_add_last : forall x (s : seq d), rotr 1 (add_last s x) = Adds x s.
Proof. by move=> *; rewrite -rot1_adds rotK. Qed.

Lemma has_rotr : forall (a : set d) (s : seq d), has a (rotr n0 s) = has a s.
Proof. by move=> *; rewrite /rotr has_rot. Qed.

Lemma uniq_rotr : forall s : seq d, uniq (rotr n0 s) = uniq s.
Proof. by move=> *; rewrite /rotr uniq_rot. Qed.

Lemma rotrK : cancel (@rotr d n0) (rot n0).
Proof.
move=> s; case (ltnP n0 (size s)); move=> Hs.
rewrite -{1}(subKn (ltnW Hs)) -{1}[size s]size_rotr; first exact: rotK.
rewrite -{2}(rot_oversize Hs); rewrite -eqn_sub0 in Hs.
by rewrite /rotr (eqP Hs) rot0.
Qed.

Lemma rotr_inj : injective (@rotr d n0).
Proof. exact (can_inj rotrK). Qed.

Lemma rev_rot : forall s : seq d, rev (rot n0 s) = rotr n0 (rev s).
Proof.
move=> s; rewrite /rotr size_rev -{3}(cat_take_drop n0 s) {1}/rot !rev_cat.
by rewrite -size_drop -size_rev rot_size_cat.
Qed.

Lemma rev_rotr : forall s : seq d, rev (rotr n0 s) = rot n0 (rev s).
Proof.
move=> s; apply: canRL rotrK.
rewrite {1}/rotr size_rev size_rotr /rotr {2}/rot rev_cat.
set m := size s - n0; rewrite -{1}(@size_takel m _ _ (leq_subr _ _)).
by rewrite -size_rev rot_size_cat -rev_cat cat_take_drop.
Qed.

End RotrLemmas.

Section RotCompLemmas.

Variable d : eqType.

Lemma rot_addn : forall m n (s : seq d), m + n <= size s ->
  rot (m + n) s = rot m (rot n s).
Proof.
move=> m n s; rewrite leq_eqVlt; case/setU1P=> [Emn|Hmn].
  by rewrite Emn rot_size -{1}(rotrK m s) /rotr -Emn addKn.
rewrite -{1}(cat_take_drop n s) /rot !take_cat !drop_cat.
rewrite addnC in Hmn; have Hn := leq_trans (leq_addr _ _) (ltnW Hmn).
rewrite (size_takel Hn) ltnNge leq_addl addnK /= catA.
by rewrite ltnNge size_drop leq_subLR -ltnNge Hmn.
Qed.

Lemma rotS : forall n (s : seq d), n < size s -> rot (S n) s = rot 1 (rot n s).
Proof. exact: rot_addn 1. Qed.

Lemma rot_add_mod : forall m n (s : seq d), n <= size s -> m <= size s ->
  rot m (rot n s) = rot (if m + n <= size s then m + n else m + n - size s) s.
Proof.
move=> m n s Hn Hm; case: (leqP (m + n) (size s)) => [Hmn|Hmn].
  exact (esym (rot_addn Hmn)).
have Hm': m + n - size s <= m by rewrite leq_subLR addnC leq_add2r.
rewrite -{1 2}(subnKl Hm') in Hm |- *.
rewrite rot_addn ?size_rot //; congr rot.
rewrite -(subn_add2r n) -subn_sub (subKn (ltnW Hmn)) -(size_rot n).
exact (rotK n s).
Qed.

Lemma rot_rot : forall m n (s : seq d), rot m (rot n s) = rot n (rot m s).
Proof.
move=> m n s; case: (ltnP (size s) m) => Hm.
  by rewrite !(@rot_oversize d m) ?size_rot 1?ltnW.
case: (ltnP (size s) n) => Hn.
  by rewrite !(@rot_oversize d n) ?size_rot 1?ltnW.
by rewrite !rot_add_mod 1?addnC.
Qed.

Lemma rot_rotr : forall m n (s : seq d), rot m (rotr n s) = rotr n (rot m s).
Proof. by move=> *; rewrite {2}/rotr size_rot rot_rot. Qed.

Lemma rotr_rotr : forall m n (s : seq d), rotr m (rotr n s) = rotr n (rotr m s).
Proof. by move=> *; rewrite /rotr !size_rot rot_rot. Qed.

End RotCompLemmas.

Section Sieve.

Variables (n0 : nat) (d : eqType).

Fixpoint sieve (m : bitseq) (s : seq d) {struct m} : seq d :=
  match m, s with
  | Adds b m', Adds x s' => if b then Adds x (sieve m' s') else sieve m' s'
  | _, _ => seq0
  end.

Lemma sieve_false : forall s n, sieve (seqn n false) s = seq0.
Proof. by elim=> [|x s Hrec] [|n] /=. Qed.

Lemma sieve_true : forall s n, size s <= n -> sieve (seqn n true) s = s.
Proof. by elim=> [|x s Hrec] [|n] //= Hn; congr Adds; apply: Hrec. Qed.

Lemma sieve0 : forall m, sieve m seq0 = seq0.
Proof. by case. Qed.

Lemma sieve1 : forall b x, sieve (Seq b) (Seq x) = seqn b x.
Proof. by case. Qed.

Lemma sieve_adds : forall b m x s,
  sieve (Adds b m) (Adds x s) = cat (seqn b x) (sieve m s).
Proof. by case. Qed.

Lemma size_sieve : forall m s, size m = size s -> size (sieve m s) = count id m.
Proof. by elim=> [|b m Hrec] [|x s] //= [Hs]; case: b; rewrite /= Hrec. Qed.

Lemma sieve_cat : forall m1 s1, size m1 = size s1 ->
  forall m2 s2, sieve (cat m1 m2) (cat s1 s2) = cat (sieve m1 s1) (sieve m2 s2).
Proof.
move=> m1 s1 Hm1 m2 s2; elim: m1 s1 Hm1 => [|b1 m1 Hrec] [|x1 s1] //= [Hm1].
by rewrite (Hrec _ Hm1); case b1.
Qed.

Lemma mem_sieve_adds : forall b m x s y,
  sieve (Adds b m) (Adds x s) y = b && (x == y) || sieve m s y.
Proof. by case. Qed.

Lemma mem_sieve : forall m s, sub_set (sieve m s) s.
Proof.
move=> m s y; elim: s m => [|x p Hrec] [|[|] m] //=; rewrite /setU1;
 case (x == y); simpl; eauto.
Qed.

Lemma has_sieve_adds : forall a b m x s,
  has a (sieve (Adds b m) (Adds x s)) = b && a x || has a (sieve m s).
Proof. by move=> a [|]. Qed.

Lemma uniq_sieve : forall s, uniq s -> forall m, uniq (sieve m s).
Proof.
elim=> [|x s Hrec] /= Hs [|b m] //.
move/andP: Hs b => [Hx Hs] [|] /=; rewrite {}Hrec // andbT.
apply/negP => [Hmx]; case/negP: Hx; exact (mem_sieve Hmx).
Qed.

Lemma sieve_rot : forall m s, size m = size s ->
 sieve (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (sieve m s).
Proof.
move=> m s Hs; have Hsn0: (size (take n0 m) = size (take n0 s)).
  by rewrite !size_take Hs.
rewrite -(size_sieve Hsn0) {1 2}/rot sieve_cat ?size_drop ?Hs //.
rewrite -{4}(cat_take_drop n0 m) -{4}(cat_take_drop n0 s) sieve_cat //.
by rewrite rot_size_cat.
Qed.

Lemma mem_sieve_rot : forall m s, size m = size s ->
  sieve (rot n0 m) (rot n0 s) =1 sieve m s.
Proof. by move=> m s Hm x; rewrite sieve_rot // mem_rot. Qed.

End Sieve.

Section Map.

Variables (n0 : nat) (d1 : eqType) (x1 : d1).
Variables (d2 : eqType) (x2 : d2) (f : d1 -> d2).

Fixpoint maps (s : seq d1) : seq d2 :=
  if s is Adds x s' then Adds (f x) (maps s') else seq0.

Lemma maps_adds : forall x s, maps (Adds x s) = Adds (f x) (maps s).
Proof. done. Qed.

Lemma maps_seqn : forall x, maps (seqn n0 x) = seqn n0 (f x).
Proof. by move=> x; elim: n0 => // *; congr Adds. Qed.

Lemma maps_cat : forall s1 s2, maps (cat s1 s2) = cat (maps s1) (maps s2).
Proof. by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec. Qed.

Lemma size_maps : forall s, size (maps s) = size s.
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma behead_maps : forall s, behead (maps s) = maps (behead s).
Proof. by case. Qed.

Lemma sub_maps : forall n s, n < size s -> sub x2 (maps s) n = f (sub x1 s n).
Proof. by move=> n s; elim: s n => [|x s Hrec] [|n]; try exact (Hrec n). Qed.

Lemma maps_add_last : forall s x, maps (add_last s x) = add_last (maps s) (f x).
Proof. by move=> *; rewrite -!cats1 maps_cat. Qed.

Lemma last_maps : forall s x, last (f x) (maps s) = f (last x s).
Proof. by elim=> [|y s Hrec] x /=. Qed.

Lemma belast_maps : forall s x, belast (f x) (maps s) = maps (belast x s).
Proof. by elim=> [|y s Hrec] x //=; rewrite Hrec. Qed.

Lemma filter_maps : forall a s, filter a (maps s) = maps (filter (comp a f) s).
Proof.
by move=> a; elim=> [|x s Hrec] //=; rewrite !if_arg (fun_if maps) /= Hrec.
Qed.

Lemma find_maps : forall a s, find a (maps s) = find (comp a f) s.
Proof. by move=> a; elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma has_maps : forall a s, has a (maps s) = has (comp a f) s.
Proof. by move=> a; elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma count_maps : forall a s, count a (maps s) = count (comp a f) s.
Proof. by move=> a; elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma maps_take : forall s, maps (take n0 s) = take n0 (maps s).
Proof. by elim: n0 => [|n Hrec] [|x s] //=; rewrite Hrec. Qed.

Lemma maps_drop : forall s, maps (drop n0 s) = drop n0 (maps s).
Proof. by elim: n0 => [|n Hrec] [|x s] //=; rewrite Hrec. Qed.

Lemma maps_rot : forall s, maps (rot n0 s) = rot n0 (maps s).
Proof. by move=> *; rewrite /rot maps_cat maps_take maps_drop. Qed.

Lemma maps_rotr : forall s, maps (rotr n0 s) = rotr n0 (maps s).
Proof.
by move=> *; apply: canRL (@rotK n0 d2); rewrite -maps_rot rotrK.
Qed.

Lemma maps_rev : forall s, maps (rev s) = rev (maps s).
Proof. by elim=> [|x s Hrec] //=; rewrite !rev_adds -!cats1 maps_cat Hrec. Qed.

Lemma maps_sieve : forall m s, maps (sieve m s) = sieve m (maps s).
Proof. by elim=> [|[|] m Hrec] [|x p] //=; rewrite Hrec. Qed.

Lemma maps_f : forall (s : seq d1) x, s x -> maps s (f x).
Proof.
move=> s x; elim: s => [|y s Hrec] //=.
by case/setU1P=> [Dx|Hx]; [ rewrite Dx setU11 | apply setU1r; auto ].
Qed.

Lemma mapsP : forall (s : seq d1) y,
  reflect (exists2 x, s x & f x = y) (maps s y).
Proof.
move=> s y; elim: s => [|x s Hrec]; first by right; case.
rewrite /= /setU1; case Hxy: (f x == y).
  by left; exists x; [ rewrite set11 | rewrite (eqP Hxy) ].
apply: (iffP Hrec) => [[x' Hx' <-]|[x' Hx' Dy]].
  by exists x'; first by rewrite Hx' orbT.
by case: Dy Hxy => <-; case: (x =P x') Hx' => [<-|_]; [rewrite set11 | exists x'].
Qed.

Lemma maps_uniq : forall s, uniq (maps s) -> uniq s.
Proof.
elim=> [|x s Hrec] //=; case/andP=> [Hsx Hs]; rewrite (Hrec Hs) andbT.
by apply/negP => Hx; case/mapsP: Hsx; exists x.
Qed.

Hypothesis Hf : injective f.

Lemma mem_maps : forall s x, maps s (f x) = s x.
Proof.
move=> s x; apply/mapsP/idP; last by exists x.
by move=> [y Hy Hfy]; rewrite -(Hf Hfy).
Qed.

Lemma index_maps : forall s x, index (f x) (maps s) = index x s.
Proof.
move=> s x; rewrite /index; elim: s => [|y s Hrec] //=.
by rewrite (inj_eq Hf) Hrec.
Qed.

Lemma uniq_maps : forall s, uniq (maps s) = uniq s.
Proof. by elim=> [|x s Hrec] //=; rewrite mem_maps /= Hrec. Qed.

Lemma inj_maps : injective maps.
Proof.
move=> s1 s2; elim: s1 s2 => [|y1 s1 Hrec] [|y2 s2] //= [Hy Hs].
by rewrite (Hf Hy) (Hrec _ Hs).
Qed.

End Map.

Implicit Arguments mapsP [d1 d2 f s y].
Prenex Implicits mapsP.

Lemma filter_sieve : forall d a (s : seq d), filter a s = sieve (maps a s) s.
Proof. by move=> d a; elim=> //= [x s <-]; case: (a x). Qed.

Section MapComp.

Variable d1 d2 d3 : eqType.

Lemma maps_id : forall s : seq d1, maps (fun x => x) s = s.
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma eq_maps : forall f1 f2 : d1 -> d2, f1 =1 f2 -> maps f1 =1 maps f2.
Proof. by move=> f1 f2 Ef; elim=> [|x s Hrec] //=; rewrite Ef Hrec. Qed.

Lemma maps_comp : forall (f1 : d2 -> d3) (f2 : d1 -> d2) s,
 maps (comp f1 f2) s = maps f1 (maps f2 s).
Proof. by move=> f1 f2; elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

Lemma mapsK : forall (f1 : d1 -> d2) (f2 : d2 -> d1),
 cancel f1 f2 -> cancel (maps f1) (maps f2).
Proof. by move=> f1 f2 Hf; elim=> [|x s Hrec] //=; rewrite Hf Hrec. Qed.

End MapComp.

(* Filter to a sub_eqType. *)

Section SubFilter.

Variables (d : eqType) (a : set d).

Fixpoint subfilter (s : seq d) : seq (sub_eqType a) :=
  if s is Adds x s' then
    if insub a x is Some u then Adds u (subfilter s') else subfilter s'
  else seq0.

Lemma val_subfilter : forall s, maps val (subfilter s) = filter a s.
Proof.
by elim=> //= [x s <-]; case: insubP => /= [_ -> -> // |]; move/negbET->.
Qed.

Lemma size_subfilter : forall s, size (subfilter s) = count a s.
Proof. by move=> s; rewrite count_filter -val_subfilter size_maps. Qed.

Lemma mem_subfilter : forall s, subfilter s =1 preimage val (setI a s).
Proof.
move=> s u; rewrite /preimage -mem_filter -val_subfilter mem_maps //.
exact: val_inj.
Qed.

Lemma uniq_subfilter : forall s, uniq s -> uniq (subfilter s).
Proof.
move=> s; move/(uniq_filter a); rewrite -val_subfilter; exact: maps_uniq.
Qed.
 
End SubFilter.

(* Index sequence *)

Fixpoint iota (m n : nat) {struct n} : natseq :=
  if n is S n' then Adds m (iota (S m) n') else seq0.

Lemma size_iota : forall m n, size (iota m n) = n.
Proof. by move=> m n; elim: n m => //= [n IHn] m; rewrite IHn. Qed.

Lemma iota_add : forall m n1 n2,
  iota m (n1 + n2) = cat (iota m n1) (iota (m + n1) n2).
Proof.
move=> m n1 n2; elim: n1 m => //= [|n1 IHn1] m; first by rewrite addn0.
by rewrite -addSnnS -IHn1.
Qed.

Lemma sub_iota : forall m n i, i < n -> sub 0 (iota m n) i = m + i.
Proof.
move=> m n i Hi; rewrite -(subnKl Hi) addSnnS iota_add.
by rewrite sub_cat size_iota ltnn subnn.
Qed.

Lemma mem_iota : forall m n i, iota m n i = (m <= i) && (i < m + n).
Proof.
move=> m n i; elim: n m => [|n IHn] /= m.
  by rewrite addn0 ltnNge andb_negb_r.
rewrite -addSnnS leq_eqVlt /setU1.
case: eqP => [->|_]; [by rewrite leq_addr | exact: IHn].
Qed.

Lemma uniq_iota : forall m n, uniq (iota m n).
Proof.
by move=> m n; elim: n m => //= [n IHn] m; rewrite mem_iota ltnn /=.
Qed.

(* Making a sequence of a specific length, using indexes to compute items. *)

Section MakeSeq.

Variables (d : eqType) (x0 : d).

Definition mkseq f n : seq d := maps f (iota 0 n).

Lemma size_mkseq : forall f n, size (mkseq f n) = n.
Proof. by move=> f n; rewrite /mkseq size_maps size_iota. Qed.

Lemma eq_mkseq : forall f g, f =1 g -> mkseq f =1 mkseq g.
Proof. move=> f g Efg n; exact: eq_maps Efg _. Qed.

Lemma uniq_mkseq : forall f n, injective f -> uniq (mkseq f n).
Proof. by move=> *; rewrite /mkseq uniq_maps // uniq_iota. Qed.

Lemma sub_mkseq : forall f n i, i < n -> sub x0 (mkseq f n) i = f i.
Proof.
by move=> f n i Hi; rewrite /mkseq (sub_maps 0) ?sub_iota ?size_iota.
Qed.

Lemma mkseq_sub : forall s, mkseq (sub x0 s) (size s) = s.
Proof.
move=> s; apply: (@eq_from_sub _ x0); rewrite size_mkseq // => i Hi.
by rewrite sub_mkseq.
Qed.

End MakeSeq.

Section FoldRight.

Variables (d : eqType) (R : Type) (f : d -> R -> R) (z0 : R).

Fixpoint foldr (s : seq d) : R :=
  if s is Adds x s' then f x (foldr s') else z0.

End FoldRight.

Section FoldRightComp.

Variables (d1 d2 : eqType) (h : d1 -> d2).
Variables (R : Type) (f : d2 -> R -> R) (z0 : R).

Lemma foldr_cat :
  forall s1 s2 : seq d2, foldr f z0 (cat s1 s2) = foldr f (foldr f z0 s2) s1.
Proof. by move=> s1 s2; elim: s1 => [|x s1 Hrec] //=; rewrite Hrec. Qed.

Lemma foldr_maps :
  forall s : seq d1, foldr f z0 (maps h s) = foldr (fun x z => f (h x) z) z0 s.
Proof. by elim=> [|x s Hrec] //=; rewrite Hrec. Qed.

End FoldRightComp.

Section FoldLeft.

Variables (d : eqType) (R : Type) (f : R -> d -> R).

Fixpoint foldl (z : R) (s : seq d) {struct s} : R :=
  if s is Adds x s' then foldl (f z x) s' else z.

Lemma foldl_rev : forall z s, foldl z (rev s) = foldr (fun x z => f z x) z s.
Proof.
move=> z s; elim/last_ind: s z => [|s x Hrec] z //=.
by rewrite rev_add_last -cats1 foldr_cat -Hrec.
Qed.

Lemma foldl_cat : forall z s1 s2, foldl z (cat s1 s2) = foldl (foldl z s1) s2.
Proof.
move=> z s1 s2; rewrite -(revK (cat s1 s2)) foldl_rev rev_cat.
by rewrite foldr_cat -!foldl_rev !revK.
Qed.

End FoldLeft.

Section Scan.

Variables (d1 : eqType) (x1 : d1) (d2 : eqType) (x2 : d2).
Variables (f : d1 -> d1 -> d2) (g : d1 -> d2 -> d1).

Fixpoint pairmap (x : d1) (s : seq d1) {struct s} : seq d2 :=
  if s is Adds y s' then Adds (f x y) (pairmap y s') else seq0.

Lemma size_pairmap : forall x s, size (pairmap x s) = size s.
Proof. by move=> x s; elim: s x => [|y s Hrec] x //=; rewrite Hrec. Qed.

Lemma sub_pairmap : forall s n, n < size s ->
  forall x, sub x2 (pairmap x s) n = f (sub x1 (Adds x s) n) (sub x1 s n).
Proof. by elim=> [|y s Hrec] [|n] //= Hn x; apply: Hrec. Qed.

Fixpoint scanl (x : d1) (s : seq d2) {struct s} : seq d1 :=
  if s is Adds y s' then let x' := g x y in Adds x' (scanl x' s') else seq0.

Lemma size_scanl : forall x s, size (scanl x s) = size s.
Proof. by move=> x s; elim: s x => [|y s Hrec] x //=; rewrite Hrec. Qed.

Lemma sub_scanl : forall s n, n < size s ->
  forall x, sub x1 (scanl x s) n = foldl g x (take (S n) s).
Proof. by elim=> [|y s Hrec] [|n] Hn x //=; rewrite ?take0 ?Hrec. Qed.

Lemma scanlK :
  (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
Proof. by move=> Hfg x s; elim: s x => [|y s Hrec] x //=; rewrite Hfg Hrec. Qed.

Lemma pairmapK : 
  (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
Proof. by move=> Hgf x s; elim: s x => [|y s Hrec] x //=; rewrite Hgf Hrec. Qed.

End Scan.

Prenex Implicits sieve maps foldr foldl scanl pairmap.

Section Zip.

Variables d1 d2 : eqType.

Fixpoint zip (s1 : seq d1) (s2 : seq d2) {struct s2}
            : seq (prod_eqType d1 d2) :=
  match s1, s2 with
  | Adds x1 s1', Adds x2 s2' => Adds (EqPair x1 x2) (zip s1' s2')
  | _, _ => seq0
  end.

Definition unzip1 := maps (@eq_pi1 d1 d2).
Definition unzip2 := maps (@eq_pi2 d1 d2).

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

(* Alternative constructor notation.                                          *)

Notation "'Seq'" := seq0 (at level 100, only parsing).

Notation "'Seq' x1 & s" := (Adds x1 s) (only parsing) : seq_scope.

Unset Implicit Arguments.





