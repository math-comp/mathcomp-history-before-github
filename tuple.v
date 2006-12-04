Require Import ssreflect.
Require Import seq.
Require Import eqtype.
Require Import ssrnat.
Require Import funs.
Require Import ssrbool.
Require Import fintype.
Require Import connect.
Require Import paths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section TupleType.

Variables (d : eqType) (n : nat).

(* homogeneous n-tuples of elements in d *)
CoInductive tupleType : Type := 
  Tuple (val:seq d) : size val = n -> tupleType.

Definition tval : tupleType -> seq d :=
  fun x => match x with Tuple val _ => val end.

Definition tproof : forall u, size (tval u) = n :=
  fun x => match x return size (tval x) = n with
           | Tuple _ proof => proof end.

Lemma tuple_eqP : reflect_eq (fun u v => tval u == tval v).
Proof.
move=> [u Hu] [v Hv]; apply: (iffP eqP) => [Huv|->] //=.
by simpl in Huv; rewrite Huv in Hu |- *; rewrite (nat_irrelevance Hu Hv).
Qed.

Canonical Structure tuple_eqType := EqType tuple_eqP.

Lemma tval_eqE : forall u v : tuple_eqType, (tval u == tval v) = (u == v).
Proof. done. Qed.

Lemma tval_inj : injective tval.
Proof. by move => u v; move/eqP; move/tuple_eqP. Qed.

Coercion tval : tupleType >-> seq.

(* operation: check if a seq is a valid tuple *)
Definition intuple (s : seq d) : option tupleType :=
  if size s =P n is Reflect_true Hs then Some (Tuple Hs) else None.

CoInductive intuple_spec (s : seq d) : option tupleType -> Type :=
  | Some_tup u : size s = n -> tval u = s -> intuple_spec s (Some u)
  | None_tup: ~~ (size s == n) -> intuple_spec s None.

Lemma intupleP : forall s, intuple_spec s (intuple s).
Proof. by rewrite /intuple => s; case: eqP; [left | right; exact/eqP]. Qed.

Definition intupleseq : seq (seq_eqType d) -> seq tuple_eqType:=
  foldr (fun (s:seq d) ts => if intuple s is Some u then Adds u ts else ts) seq0.

Lemma mem_intupleseq : forall a, intupleseq a =1 (fun u => a u).
Proof.
elim=> // s a IHa u /=.
case: intupleP => [v _ Dv | Hs]; rewrite /= /setU1 IHa -?Dv //.
by case: eqP => // Ds; case/eqP: Hs; rewrite Ds tproof.
Qed.

Lemma uniq_intupleseq : forall s, uniq s -> uniq (intupleseq s).
Proof.
elim => // e s IH Hes. 
rewrite uniq_adds in Hes;move/andP: Hes => [He Hs] /=;have:=IH Hs.
case: intupleP => // u Hu Du Hins; rewrite uniq_adds.
by apply/andP; split => //; rewrite mem_intupleseq Du.
Qed.

End TupleType.

(* fin_type of tuples of length n over fin_type d *)
Section finTuple.

Variable d : finType.
Variable n : nat.
 
(* type abbreviation *)

Let seq2 := seq (seq_eqType d). 

(* Adds e to every element of s *)
Let multes (e:d) s := maps (Adds e) s. 

Let multss (s : seq d) (s1 : seq2) :=
  foldr (fun x => cat (multes x s1)) seq0 s.

(*
Eval compute in multss (Seq x1 x2) (Seq (Seq x3 x4) (Seq x5 x6)).
-> Seq (Seq x1 x3 x4) (Seq x1 x5 x6) (Seq x2 x3 x4) (Seq x2 x5 x6)
*)

(* the sequence of all the strings of length m on the d alphabet *)
Definition mkpermr m := iter m (multss (enum d)) (Seq seq0).

(* the sequence of all the n-tuples on the d alphabet *)
Definition fintuple_enum := intupleseq n (mkpermr n).

Lemma mem_multes : forall y s2,
  multes y s2 =1 (fun s => if s is Adds x s' then (x == y) && s2 s' else false).
Proof.
move=> y s2 s; elim: s2 => [|s' s2 IHs2] /=; first by case: s => // *; rewrite andbF.
by rewrite /setU1 {}IHs2; case: s => //= x s; rewrite (eq_sym x) demorgan1.
Qed.

Lemma mem_multss : forall s1 s2,
  multss s1 s2 =1 (fun s => if s is Adds x s' then s1 x && s2 s' else false).
Proof.
move=> s1 s2 s; elim: s1 => [|y s1 IHs1] /=; first by case s.
by rewrite mem_cat /setU {}IHs1 mem_multes; case: s => //= x s; rewrite -demorgan2 eq_sym.
Qed.

Lemma mem_mkpermr_size : forall m, mkpermr m =1 (fun s => size s == m).
Proof. by elim=> [|i IHi] [|x s] //=; rewrite mem_multss // mem_enum IHi. Qed.

Lemma maps_tval_fintuple_enum: 
  maps (@tval d n) fintuple_enum = mkpermr n.
Proof.
rewrite /fintuple_enum.
have: all (fun s => size s == n) (mkpermr n).
  by apply/allP => s; rewrite mem_mkpermr_size.
elim: (mkpermr n) => //= s s2 IHs; move/andP => [Hs Hs2].
by case: intupleP => [_ _ /= ->|]; [rewrite (IHs Hs2)|rewrite Hs].
Qed.

Lemma uniq_mkpermr : forall m, uniq (mkpermr m).
Proof.
elim=> //= i IHi; elim: enum (uniq_enum d) => //= x e IHe.
move/andP=> [Hx He]; rewrite uniq_cat {}IHe {He}// andbT.
rewrite {1}/multes uniq_maps ?{}IHi; last move=> _ _ [] //.
apply/hasP; case=> s Hs.
by move/mapsP => [s' _ Ds]; rewrite mem_multss -Ds (negbE Hx) in Hs.
Qed.

  (* good enumeration *)
Lemma fintuple_enumP : forall u, count (set1 u) fintuple_enum = 1.
Proof.
move => [s ps]. 
rewrite /fintuple_enum count_set1_uniq; last exact (uniq_intupleseq n (uniq_mkpermr n)).
by rewrite mem_intupleseq /= mem_mkpermr_size ps set11.
Qed.

Canonical Structure tup_finType := FinType fintuple_enumP.

End finTuple.


(*  if a is a family of sets, the tuple (u0,...,u_n-1) belongs to (tuple_prod n a) iff
  a 0 u0 && a 1 u1 && .. && a n-1 u_n-1 *)

Section TupleProd.

Variable d : eqType.
Variable x0 : d.
Variable n : nat.
Variable a : nat -> set d.

Fixpoint tuple_prod_seq (i:nat) (s : seq d) {struct s} : bool :=
  if s is Adds x s' then (a i x && tuple_prod_seq (S i) s') else true.

(* Characteristic function of (tuple_prod n a) over (seq d) *)
Definition tuple_prod : set (tuple_eqType d n) :=
  fun u => tuple_prod_seq 0 u.

Lemma tuple_prodP: forall u : tupleType d n, 
  reflect (forall i, i < n -> a i (sub x0 u i)) (tuple_prod u).
Proof.
rewrite /tuple_prod -[a]/(fun i => a (0 + i)) => [[s /= <-]].
elim: s 0 => [|x s IHs] i /=; first by left.
rewrite -{2}[i]addn0. case Hx: (a _ x); last
  by right=> Hs; case/idP: Hx; exact: (Hs 0).
apply: {IHs}(iffP (IHs _)) => Hs j; last by rewrite -ltnS addSnnS; move/Hs.
case: j => // j; rewrite -addSnnS; exact: Hs.
Qed.

End TupleProd.


Lemma card_tuple_prod: 
 forall t, forall n,
 forall a : nat -> set (FinType.sort t),
  card (@tuple_prod _ n a) = 
    foldr (fun i m => card (a i) * m) 1 (iota 0 n).
Proof.
rewrite {1}/card => t n a /=. 
rewrite count_filter /tuple_prod -(size_maps (@tval _ _)).
rewrite -(filter_maps (@tval t n) (tuple_prod_seq a 0)) -count_filter.
rewrite maps_tval_fintuple_enum.
elim: n {-2}0 => //= n IH i; rewrite -{}IH {1}/card.
elim: enum => //= x e IHe; rewrite muln_addl -{}IHe count_cat; congr addn.
rewrite count_filter filter_maps size_maps -count_filter /comp /=.
case: (a i x) => //=; exact: count_set0.
Qed.

Section FinGraph.

Variable d1 d2 : finType.

(* the graph of functions f from d1 to d2 : (f e1, f e2, ...) where (enum d1) = e1::e2::_ *)
Definition fgraphType := tupleType d2 (size (enum d1)).

Canonical Structure fgraph_eqType := @EqType fgraphType _ (@tuple_eqP _ _).
Canonical Structure fgraph_finType :=
  @FinType fgraph_eqType _ (@fintuple_enumP _ _).

Definition graph_of_fun (f : d1 -> d2) : fgraphType := Tuple (size_maps f _).

 (* if the domain is not empty the default is the first elem of the graph *)
Lemma fgraph_default : d1 -> fgraphType -> d2.
Proof. by move=> x [[|//]]; case: enum (mem_enum x). Qed.

Definition fun_of_graph g x := sub (fgraph_default x g) g (index x (enum d1)).

Coercion fun_of_graph : fgraphType >-> Funclass.

Lemma can_fun_of_graph : cancel fun_of_graph graph_of_fun.
Proof.
rewrite /fun_of_graph => g; case: {-1}g => s Hs; apply: tval_inj => /=.
case De: (enum _) => [|x0 e]; first by case: s Hs; rewrite De. 
rewrite -De; have y0 := fgraph_default x0 g.
apply: (@eq_from_sub _ y0); rewrite size_maps // => i Hi.
by rewrite (sub_maps x0) // index_uniq ?uniq_enum ?(set_sub_default y0) ?Hs.
Qed.

Lemma can_graph_of_fun : forall f, graph_of_fun f =1 f.
Proof.
rewrite /fun_of_graph /= => f x.
by rewrite (sub_maps x) ?sub_index // ?index_mem mem_enum.
Qed.

End FinGraph.

(*m ^ n*)
Definition expn m n := iter n (muln m) 1.
 
Section Tfunspace.

Variables d1 d2 : finType.

Variable a2 : set d2.

(* total functions d1 -> d2, but codomains are restricted to a2 (included in d2) *)
Definition tfunspace : set (fgraph_eqType d1 d2) := tuple_prod (fun _ => a2).

(* # (d1 -> a2) = #a2 ^ #d1 *)
Lemma card_tfunspace : card tfunspace = expn (card a2) (card d1).
Proof.
rewrite /tfunspace. 
have := card_tuple_prod.
rewrite /tup_finType /fgraph_finType /tuple_eqType /fgraph_eqType /fgraphType.
by move ->; rewrite -cardA; elim: (card d1) {2}0 => //= n IHn i; rewrite IHn.
Qed.

End Tfunspace.

Section Pfunspace.

Variables d1 d2 : finType.
Variable y0 : d2.
Variable a1 : set d1.
Variable a2 : set d2.

(* singleton of a default element chosen in the codomain universe *)
Let a2' := set1 y0. 

(* notice that : sub false (maps a1 (enum d1)) i = a1 (sub _ (enum d1) i)  *)
(* subset of fgraphs corresponding to a1 -> a2 functions *)
Definition pfunspace :=
  @tuple_prod _ (card d1) (fun i => if sub false (maps a1 (enum d1)) i then a2 else a2').

Lemma iota_addl : forall m1 m2 n,
  iota (m1 + m2) n = maps (addn m1) (iota m2 n).
Proof. by move=> m1 m2 n; elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.

Lemma card_pfunspace: card pfunspace = expn (card a2) (card a1).
Proof. 
rewrite /pfunspace card_tuple_prod. rewrite {2 4}/card.
elim: (enum d1) => //= x e IHe.
rewrite -{2}add1n iota_addl foldr_maps /= {}IHe.
by case: (a1 x) => //=; rewrite /a2' card1 mul1n.
Qed.

Definition support f : set d1 := fun x => setC1 (f x) y0.

Lemma pfunspaceP : forall g : fgraphType d1 d2,
  reflect (sub_set (support g) a1 /\ sub_set (image g a1) a2) (pfunspace g).
Proof.
pose e1 := enum d1.
have He1 : index _ e1 < size e1 by move=> x1; rewrite index_mem /e1 mem_enum.
move=> g; apply: (iffP (tuple_prodP y0 _ _)) => [Hg | [Hg1 Hg2] i Hi].
  split=> [x1 Hx1 | x2 Hx2].
    apply/negPf=> Hx1'; case/negP: Hx1; rewrite eq_sym /fun_of_graph.
    have Hi := He1 x1; rewrite (set_sub_default y0) ?tproof //.
    by move: {Hg}(Hg _ Hi); 
       rewrite (sub_maps x1) // sub_index /e1 ?mem_enum ?Hx1'.
  case/set0Pn: Hx2=> x1; case/andP; move/eqP=> -> {x2} Hx1.
  have Hi := He1 x1; rewrite /fun_of_graph (set_sub_default y0) ?tproof //.
  by move: {Hg}(Hg _ Hi); rewrite (sub_maps x1) // sub_index /e1 ?mem_enum ?Hx1.
cut d1; last by move: Hi; rewrite /card; case: (enum d1); auto.
move => x0.
rewrite (sub_maps x0) //; set x1 := sub _ _ i.
have <-: g x1 = sub y0 (@tval _ (card d1) g) i.
  by rewrite /fun_of_graph (set_sub_default y0) /x1 ?index_uniq ?tproof ?uniq_enum.
case Hx1: (a1 x1).
  by apply: Hg2; apply/set0Pn; exists x1; rewrite /setI /preimage set11.
by apply/idPn=> Hx1'; case/idP: Hx1; apply: Hg1; rewrite /support /setC1 eq_sym.
Qed.

End Pfunspace.

Section FinPowerSet.

Variable d : finType.
Variable a : set d.

Definition powerset := pfunspace false a bool_eqType.

Lemma card_powerset : card powerset = expn 2 (card a).
Proof. exact: card_pfunspace. Qed.

End FinPowerSet.

(* Implicit Arguments powerset []. *)
Notation "'<<' x , .. , y '>>'" := 
  (Tuple (refl_equal (size (Adds x .. (Adds y seq0) ..)))).

Section Sample.

Check <<2,3,4>>.
Check <<2,3,4>> 3.
Eval compute in <<2,3,4>> 3.
Definition a : nat_eqType -> set nat_eqType := 
  fun n => if n is O then set1 2 else if n is S O then set3 1 2 3 else set0.
Check tuple_prod a <<2,3>>.
Eval compute in tuple_prod a <<2,3>>.
Eval compute in tuple_prod a <<2,3,1>>.
CoInductive FT: Type := A | B | C.
Definition eqFT (x y:FT) : bool := 
  match x,y with A,A => true | B,B => true | C,C => true | _,_ => false end.
Lemma eqFTP: reflect_eq eqFT. 
Proof. 
by rewrite /reflect_eq; case; case; constructor.
Qed.
Canonical Structure FT_eqType := EqType eqFTP.
Definition FT_enum : seq_eqType FT_eqType := Seq A B C.
Lemma FT_enumP: forall x, count (set1 x) FT_enum = 1.
Proof. 
rewrite /FT_enum /=. 
by case => /=; rewrite ?addn0 ?add0n.
Qed.
Canonical Structure FT_finType := FinType FT_enumP.
Check powerset.
Let g : fgraphType FT_finType _ := <<true,true,false>>.
Eval compute in powerset FT_eqType g.
Eval compute in g A.
Eval compute in g C.

End Sample.

Unset Implicit Arguments.
