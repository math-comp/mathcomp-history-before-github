Require Import ssreflect.
Require Import seq.
Require Import eqtype.
Require Import ssrnat.
Require Import funs.
Require Import ssrbool.
Require Import fintype.
Require Import connect.
Require Import paths.
Require Import div.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FgraphProd.

Variables (d1 : finType) (d2 : eqType).
Variable a : d1 -> set d2.

Fixpoint prod_seq (s1:seq d1) (s2 : seq d2) {struct s1} : bool :=
  match s1, s2 with
  | Adds x1 s1', Adds x2 s2' => a x1 x2 && prod_seq s1' s2'
  | _,_ => true
  end. 

(* Characteristic function of (tuple_prod n a) over (seq d) *)
Definition fgraph_prod : set (fgraph_eqType d1 d2) :=
  fun u => prod_seq (enum d1) (fval u).

Lemma seq_ind2: forall t1 t2 P, 
  (P seq0 seq0) ->
  (forall e1 e2 s1 s2, P s1 s2 -> P (Adds e1 s1) (Adds e2 s2)) ->
  forall (s1:seq t1) (s2 : seq t2), size s1 = size s2 -> P s1 s2.
Proof.
move => g1 g2 P Hseq0 Hadds.
elim => [[] //| e s IH [] // e1 s1 [Hsize1]].
by apply: Hadds; apply: (IH s1).
Qed.

Lemma fgraph_prodP: forall u : fgraphType d1 d2,
  reflect (forall x, a x (u x)) (fgraph_prod u).
Proof.
move=> u; have Hind: (size (enum d1) = size (fval u)) by case: u => /= s ->; rewrite cardA.
rewrite /fgraph_prod /=; apply: (iffP idP).
  move=> H x; have: (enum d1 x) by rewrite mem_enum.
  unlock fun_of_fgraph.
  move: (enum d1) (fval u) Hind H x; apply: seq_ind2 => //=.
  move=> e1 e2 s1 s2 IH; rewrite /prod_seq /=; move/andP=> [ae Hs] x Hx.
  case Dx: (x == e1); first by rewrite (eqP Dx).
  by rewrite /setU1 eq_sym Dx orFb in Hx; move/(_ Hs x Hx): IH.
suff: ((forall x : d1, (enum d1 x) -> a x (sub (fgraph_default x u) (fval u) (index x (enum d1)))) ->
        prod_seq (enum d1) (fval u)) by unlock fun_of_fgraph; auto.
move: (enum d1) (fval u) Hind (uniq_enum d1); apply: seq_ind2 => //=.
move=> e1 e2 s1 s2 IH Hf H; apply/andP; split.
  by move/(_ e1): H; rewrite /setU1 eq_refl /=; auto.
case/andP:Hf => He Us1; apply: (IH Us1) => x S1x.
have Dx: x != e1 by apply/negP; move/eqP=> Dx; move/negP: He; rewrite -Dx; auto.
by move/(_ x): H; rewrite (negbET Dx) /= /setU1 S1x orbT; auto.
Qed.
End FgraphProd.

Definition family := fgraph_prod.
Definition familyP := fgraph_prodP.

Definition pfamily (d : finType) d' y0 (r : set d) (a' : d -> set d') :=
  family (fun i => if r i then a' i else set1 y0).

Lemma card_fgraph_prod: 
 forall t c : finType,
 forall a : c -> set t,
  card (@fgraph_prod c t a) = 
    foldr (fun i m => card (a i) * m) 1 (enum c).
Proof.
rewrite {1}/card => t c a /=. 
rewrite count_filter /fgraph_prod -(size_maps (@fval _ _)).
rewrite -(filter_maps (@fval c t) (prod_seq a _)) -count_filter.
rewrite maps_tval_fintuple_enum cardA.
elim: (enum c) => //= e s <-; rewrite /card.
elim: (enum t) => //= e1 s1 IH; rewrite muln_addl -{}IH count_cat; congr addn.
rewrite count_filter filter_maps size_maps -count_filter /comp /=.
case: (a _ _) => //=; exact: count_set0.
Qed.

(*m ^ n*)
(*Definition expn m n := iter n (muln m) 1.*)
 
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
by elim: (enum d1) => //= e s ->.
Qed.

Lemma tfunspaceP : 
  forall u : fgraphType d1 d2, 
  reflect (forall x : d1, a2 (u x)) (tfunspace u).
Proof. by move => u; apply: (iffP idP); [move/fgraph_prodP | move=>*; apply/fgraph_prodP]. Qed.

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
  @fgraph_prod d1 _ (fun i => if a1 i then a2 else a2').

Lemma iota_addl : forall m1 m2 n,
  iota (m1 + m2) n = maps (addn m1) (iota m2 n).
Proof. by move=> m1 m2 n; elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.

Lemma card_pfunspace: card pfunspace = expn (card a2) (card a1).
Proof. 
rewrite /pfunspace /card /=.
have := card_fgraph_prod; rewrite /card /=; move ->.
rewrite /card; elim: (enum d1) => //= x e /= ->.
case: (a1 x) => //=; rewrite /a2'; have := card1; rewrite/card => ->. 
by rewrite mul1n.
Qed.

(*
Lemma pfunspaceP : 
  forall u : fgraphType d1 d2, 
  reflect (forall x : d1, (a1 x /\ a2 (u x)) \/ (~~ a1 x /\ a2' (u x))) (pfunspace u).
Proof.
rewrite /tfunspace/fun_of_fgraph -lock => u. 
apply: (iffP idP). 
  by move/fgraph_prodP => H x; move/(_ x):H; case: (a1 x)=>* ; [ left | right ].
move=> H; apply/fgraph_prodP => x; move/(_ x): H.
by case=>[[-> H //] | [Hx H]]; rewrite (negbET Hx).
Qed.
*)

Definition support f : set d1 := fun x => setC1 (f x) y0.

Lemma pfunspaceP : forall g : fgraphType d1 d2,
  reflect (sub_set (support g) a1 /\ sub_set (image g a1) a2) (pfunspace g).
Proof.
pose e1 := enum d1.
move=> g; apply: (iffP idP).
  move/fgraph_prodP => Hg.
  split=> [x1 Hx1 | x2 Hx2].
    apply/negPf=> Hx1'; case/negP: Hx1; rewrite eq_sym.
    by move: {Hg}(Hg x1); rewrite Hx1' /a2'.
  case/set0Pn: Hx2=> x1; case/andP; move/eqP=> -> {x2} Hx1.
  by move: {Hg}(Hg x1); rewrite {}Hx1. 
move=> [Hg1 Hg2]; apply/fgraph_prodP=>x.
case Hx1: (a1 x).
  apply: Hg2; apply/set0Pn; exists x.
  by rewrite /setI /preimage Hx1 eq_refl.
apply/idPn=> Hx1'; case/idP: Hx1; apply: Hg1.
by rewrite /support /setC1 eq_sym.
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
Variables (d1:eqType) (d2:finType) (n:nat).
Let domain := ordinal_finType n.

Definition tupleType := fgraphType domain d1.

Canonical Structure tule_eqType := EqType (@fgraph_eqP domain d1).
Canonical Structure tule_finType := FinType (@finfgraph_enumP domain d2).

End Tuple.

Unset Implicit Arguments.
