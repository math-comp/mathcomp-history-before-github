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

Section FgraphProd.

Variables d1 d2 : finType.
Variable x0 : d2.
Variable a : nat -> set d2.

Fixpoint prod_seq (i:nat) (s : seq d2) {struct s} : bool :=
  if s is Adds x s' then (a i x && prod_seq (S i) s') else true.

(* Characteristic function of (tuple_prod n a) over (seq d) *)
Definition fgraph_prod : set (fgraph_eqType d1 d2) :=
  fun u => prod_seq 0 (fval u).

Lemma fgraph_prodP: forall u : fgraphType d1 d2, 
  reflect (forall i, i < (card (setA d1)) -> a i (sub x0 (fval u) i)) (fgraph_prod u).
Proof.
rewrite /fgraph_prod -[a]/(fun i => a (0 + i)) => [[s /= <-]].
elim: s 0 => [|x s IHs] i /=; first by left.
rewrite -{2}[i]addn0; case Hx: (a _ x); last first.
  right=> Hs; case/idP: Hx; exact: (Hs 0).
apply: {IHs}(iffP (IHs _)) => Hs j; last by rewrite -ltnS addSnnS; move/Hs.
case: j => // j; rewrite -addSnnS; exact: Hs.
Qed.

End FgraphProd.

Lemma card_fgraph_prod: 
 forall t, forall c,
 forall a : nat -> set (FinType.sort t),
  card (@fgraph_prod c t a) = 
    foldr (fun i m => card (a i) * m) 1 (iota 0 (card (setA c))).
Proof.
rewrite {1}/card => t c a /=. 
rewrite count_filter /fgraph_prod -(size_maps (@fval _ _)).
rewrite -(filter_maps (@fval c t) (prod_seq a 0)) -count_filter.
rewrite maps_tval_fintuple_enum.
elim: (card (setA c)) {-2}0 => //= n IH i; rewrite -{}IH {1}/card.
elim: enum => //= x e IHe; rewrite muln_addl -{}IHe count_cat; congr addn.
rewrite count_filter filter_maps size_maps -count_filter /comp /=.
case: (a i x) => //=; exact: count_set0.
Qed.

(*m ^ n*)
Definition expn m n := iter n (muln m) 1.
 
Section Tfunspace.

Variables d1 d2 : finType.

Variable a2 : set d2. 

(* total functions d1 -> d2, but codomains are restricted to a2 (included in d2) *)
Definition tfunspace : set (fgraph_eqType d1 d2) := 
  (fgraph_prod (fun _ => a2 )).

(* # (d1 -> a2) = #a2 ^ #d1 *)
Lemma card_tfunspace : card tfunspace = expn (card a2) (card (setA d1)).
Proof.
rewrite /tfunspace. 
have := card_fgraph_prod. 
rewrite /fgraph_finType /fgraph_eqType /card /fgraph_prod /=.
move => H; rewrite (H d2 d1 (fun _ => a2)).
by elim: (count (setA d1)) {2}0 => //= n IHn i; rewrite IHn.
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
  @fgraph_prod d1 _ (fun i => if sub false (maps a1 (enum d1)) i then a2 else a2').

Lemma iota_addl : forall m1 m2 n,
  iota (m1 + m2) n = maps (addn m1) (iota m2 n).
Proof. by move=> m1 m2 n; elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.

Lemma card_pfunspace: card pfunspace = expn (card a2) (card a1).
Proof. 
rewrite /pfunspace /card /=.
have := card_fgraph_prod; rewrite /card /=; move ->.
rewrite /card; elim: (enum d1) => //= x e IHe.
rewrite -{2}add1n iota_addl foldr_maps /= {}IHe.
case: (a1 x) => //=; rewrite /a2'; have := card1; rewrite/card => ->. 
by rewrite mul1n.
Qed.

Definition support f : set d1 := fun x => setC1 (f x) y0.

Lemma pfunspaceP : forall g : fgraphType d1 d2,
  reflect (sub_set (support g) a1 /\ sub_set (image g a1) a2) (pfunspace g).
Proof.
pose e1 := enum d1.
have He1 : index _ e1 < size e1 by move=> x1; rewrite index_mem /e1 mem_enum.
move=> g; apply: (iffP (fgraph_prodP y0 _ _)) => [Hg | [Hg1 Hg2] i Hi].
  split=> [x1 Hx1 | x2 Hx2].
    apply/negPf=> Hx1'; case/negP: Hx1; rewrite eq_sym; unlock fun_of_fgraph.
    have Hi := He1 x1; rewrite (set_sub_default y0) ?fproof //.
    by move: {Hg}(Hg _ Hi); 
       rewrite (sub_maps x1) // sub_index /e1 ?mem_enum ?Hx1'.
  case/set0Pn: Hx2=> x1; case/andP; move/eqP=> -> {x2} Hx1.
  have Hi := He1 x1; unlock fun_of_fgraph ;rewrite (set_sub_default y0) ?fproof //.
  by move: {Hg}(Hg _ Hi); rewrite (sub_maps x1) // sub_index /e1 ?mem_enum ?Hx1.
have x0 : d1 by move: Hi; rewrite /card; case: (enum d1); auto.
rewrite (sub_maps x0) //; set x1 := sub _ _ i.
have <-: g x1 = sub y0 (fval g) i.
  by unlock fun_of_fgraph;rewrite (set_sub_default y0) /x1; unlock;
    rewrite ?index_uniq ?fproof ?uniq_enum.
case Hx1: (a1 x1).
  by apply: Hg2; apply/set0Pn; exists x1; rewrite /setI /preimage set11.
by apply/idPn=> Hx1'; case/idP: Hx1; apply: Hg1; rewrite /support /setC1 eq_sym.
Qed.

End Pfunspace.

Section FinPowerSet.

Variable d : finType.
Variable a : set d.

Definition powerset := pfunspace false a (setA bool_eqType).

Lemma card_powerset : card powerset = expn 2 (card a).
Proof. exact: card_pfunspace. Qed.

End FinPowerSet.

Section Tuple.
Variables (d:finType) (n:nat).
Let domain := ordinal n.

Definition tupleType := fgraphType domain d.

Canonical Structure tuple_eqType := EqType (@fgraph_eqP domain d).
Canonical Structure tuple_finType := FinType (@finfgraph_enumP domain d).

End Tuple.
  
Unset Implicit Arguments.
