
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import div.
Require Import seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*   A small theory of data sets of finite cardinal, based on sequences.     *)
(* A finite data set is a data set plus a duplicate-free sequence of all its *)
(* elements. This is equivalent to reqiuiring only a list, and we do give a   *)
(* construction of a finDomain from a list, but it is preferable to specify  *)
(* the structure of the eqtype in general.                                   *)

Module FinType.

Record finType : Type := FinType {
  sort :> eqType;
  enum : seq sort;
  enumP : forall x, count (set1 x) enum = 1
}.

End FinType.

Notation finType := FinType.finType.
Notation FinType := FinType.FinType.
Notation enum := FinType.enum.

Section SeqFinType.

Variables (d : eqType) (e : seq d).

Definition seq_enum := subfilter e (undup e).

Lemma seq_enumP : forall u, count (set1 u) seq_enum = 1.
Proof.
move=> [x Hx]; rewrite count_set1_uniq /seq_enum.
  by rewrite mem_subfilter /preimage /setI /= mem_undup Hx.
apply: uniq_subfilter; exact: uniq_undup.
Qed.

Definition seq_finType := FinType seq_enumP.

End SeqFinType.

Lemma bool_enumP : forall b, count (set1 b) (Seq true false) = 1.
Proof. by move=> [|]. Qed.

Canonical Structure bool_finType := FinType bool_enumP.

Section FiniteSet.

Variable d : finType.

Lemma mem_enum : enum d =1 (setA d).
Proof. by move=> x; rewrite -has_set1 has_count FinType.enumP. Qed.

Lemma filter_enum : forall a : set d, filter a (enum d) =1 a.
Proof. by move=> a x; rewrite mem_filter /setI andbC mem_enum. Qed.

Lemma uniq_enum : uniq (enum d).
Proof.
have: forall x, count (set1 x) (enum d) <= 1.
  by move=> x; rewrite FinType.enumP.
elim: (enum d) => [|x s Hrec] Hs //=; apply/andP; split.
  rewrite -has_set1 has_count -ltnNge /=.
  by apply: leq_trans (Hs x); rewrite /= set11 leqnn.
by apply: Hrec => y; apply: leq_trans (Hs y); rewrite /= leq_addl.
Qed.

Section Pick.

Variable a : set d.

CoInductive pick_spec : option d -> Type :=
  | Pick x : a x -> pick_spec (Some x)
  | Nopick : a =1 set0 -> pick_spec None.

Definition pick : option d :=
  if filter a (enum d) is Adds x _ then Some x else None.

Lemma pickP : pick_spec pick.
Proof.
rewrite /pick; case: (filter a (enum d)) (filter_enum a) => [|x s] Ha.
  by right; apply: fsym.
by left; rewrite -Ha /= setU11.
Qed.

End Pick.

Lemma eq_pick : forall a b, a =1 b -> pick a = pick b.
Proof. move=> a *; symmetry; rewrite /pick -(@eq_filter _ a); auto. Qed.

Section Cardinal.

Definition card a := count a (enum d).

Lemma eq_card : forall a b, a =1 b -> card a = card b.
Proof. move=> a b Eab; exact: eq_count. Qed.

Lemma eq_card_trans : forall a b n, card b = n -> a =1 b -> card a = n.
Proof. move=> a b _ <-; exact: eq_card. Qed.

Lemma card0 : card set0 = 0. Proof. exact: count_set0. Qed.

Lemma cardA : card (setA d) = size (enum d). Proof. exact: count_setA. Qed.

Lemma eq_card0 : forall a, a =1 set0 -> card a = 0.
Proof. by have:= eq_card_trans card0. Qed.

Lemma eq_cardA : forall a, a =1 (setA d) -> card a = size (enum d).
Proof. by have:= eq_card_trans cardA. Qed.

Lemma card1 : forall x, card (set1 x) = 1.
Proof. move=> x; exact: FinType.enumP. Qed.

Lemma cardUI : forall a b, card (setU a b) + card (setI a b) = card a + card b.
Proof. move=> a b; exact: count_setUI. Qed.

Lemma cardIC : forall b a, card (setI a b) + card (setI a (setC b)) = card a.
Proof.
by move=> b a; apply: etrans _ (add0n _); rewrite -cardUI addnC -card0;
   congr (_ + _); apply: eq_card => x; rewrite /setI /setU /setC;
   case (a x); case (b x).
Qed.

Lemma cardC : forall a, card a + card (setC a) = card (setA d).
Proof. move=> a; apply: etrans (esym cardA); exact: count_setC. Qed.

Lemma cardU1 : forall x a, card (setU1 x a) = negb (a x) + card a.
Proof.
move=> x a; apply: addn_injr (etrans (cardUI _ _) _); symmetry.
rewrite addnC addnA; congr addn; rewrite -(@eq_card (filter a (Seq x))).
  simpl; case: (a x); last by rewrite /= card0 card1.
  by rewrite addnC; apply: eq_card => y; exact: mem_seq1.
by move=> y; rewrite mem_filter /setI mem_seq1 andbC.
Qed.

Lemma card2 : forall x y, card (set2 x y) = S (x != y).
Proof.
move=> x y /=; apply: (etrans (cardU1 x (set1 y))).
by rewrite card1 addn1 eq_sym.
Qed.

Lemma cardC1 : forall x, card (setC1 x) = pred (card (setA d)).
Proof. by move=> x; rewrite -(cardC (set1 x)) card1. Qed.

Lemma cardD1 : forall x a, card a = a x + card (setD1 a x).
Proof.
move=> x a; rewrite addnC; apply: (addn_injr (etrans (cardC a) _)).
rewrite -addnA (negb_intro (a x)) -[negb (a x)]/(setC a x) -cardU1.
symmetry; apply: etrans (congr1 (addn _) _) (cardC _).
by apply: eq_card => y; rewrite /setC /setU1 /setD1 negb_andb negb_elim.
Qed.

Lemma max_card : forall a, card a <= card (setA d).
Proof. move=> a; rewrite -(cardC a); apply: leq_addr. Qed.

Lemma card_size : forall s : seq d, card s <= size s.
Proof.
elim=> [|x s Hrec] /=; first by rewrite card0.
by rewrite cardU1; case (s x); first exact (leqW Hrec).
Qed.

Lemma card_uniqP : forall s : seq d, reflect (card s = size s) (uniq s).
Proof.
move=> s; elim: s => [|x s Hrec]; first by left; exact card0.
rewrite /= cardU1 /addn; case (s x); simpl.
  by right; move=> H; move: (card_size s); rewrite H ltnn.
by apply: (iffP Hrec) => [<-| [<-]].
Qed.

End Cardinal.

Definition set0b a := card a == 0.
Definition disjoint a b := set0b (setI a b).
Definition subset a b := disjoint a (setC b).

Lemma card0_eq : forall a, card a = 0 -> a =1 set0.
Proof. by move=> a Ha x; apply/idP => [Hx]; rewrite (cardD1 x) Hx in Ha. Qed.

Lemma set0P : forall a, reflect (a =1 set0) (set0b a).
Proof. move=> a; apply: (iffP eqP); [apply: card0_eq | apply: eq_card0]. Qed.

Lemma set0Pn : forall a : set d, reflect (exists x, a x) (~~ set0b a).
Proof.
move=> a; case: (set0P a) => [Ha|Hna]; constructor.
  by move=> [x Hx]; case/idP: (Ha x).
by case: (pickP a) => [x Hx|Ha]; [ exists x | case (Hna Ha) ].
Qed.

Lemma subsetP : forall a b, reflect (sub_set a b) (subset a b).
Proof.
move=> a b; rewrite /subset /disjoint /setI /setC.
apply: (iffP (set0P _)).
  by move=> Hab x Ha; apply negbEF; rewrite -(Hab x) Ha.
by move=> Hab x; case Ha: (a x); try rewrite (Hab _ Ha).
Qed.

Lemma subset_leq_card : forall a b, subset a b -> card a <= card b.
Proof.
move=> a b; move/(set0P _)=> Hab.
rewrite -(leq_add2l (card (setC b))) 2!(addnC (card (setC b))).
rewrite -cardUI (eq_card Hab) card0 addn0 cardC; apply max_card.
Qed.

Lemma subset_refl : forall a, subset a a.
Proof. by move=> a; apply/subsetP; move. Qed.

Lemma eq_subset : forall a a', a =1 a' -> subset a =1 subset a'.
Proof.
by move=> a a' Eaa' b; congr eqn; apply: eq_card => x; rewrite /setI Eaa'.
Qed.

Lemma eq_subset_r : forall b b', b =1 b' -> forall a, subset a b = subset a b'.
Proof.
by move=> b b' Ebb' a; congr eqn; apply: eq_card => x; rewrite /setI /setC Ebb'.
Qed.

Lemma subset_setA : forall a, subset a (setA d).
Proof. by move=> a; apply/subsetP. Qed.

Lemma subsetA : forall a, subset (setA d) a -> forall x, a x.
Proof. move=> a; move/subsetP=> Ha x; auto. Qed.

Lemma subset_eqP : forall a b, reflect (a =1 b) (subset a b && subset b a).
Proof.
move=> a b; apply: (iffP andP) => [[Hab Hba] x|Eab].
  by apply/idP/idP; apply: subsetP.
by rewrite (eq_subset_r Eab) (eq_subset Eab) subset_refl.
Qed.

Lemma subset_cardP : forall a b, card a = card b -> reflect (a =1 b) (subset a b).
Proof.
move=> a b Ecab; case Hab: (subset a b) (subset_eqP a b); simpl; auto.
case: (subsetP b a) => [H|[]] // x Hbx; apply/idPn => Hax.
case/idP: (ltnn (card a)); rewrite {2}Ecab (cardD1 x b) Hbx /setD1.
apply: subset_leq_card; apply/subsetP=> y Hy; rewrite andbC.
by rewrite (subsetP _ _ Hab _ Hy); apply/eqP => Dx; rewrite Dx Hy in Hax.
Qed.

Lemma subset_trans : forall a b c, subset a b -> subset b c -> subset a c.
Proof.
move=> a b c; move/subsetP=> Hab; move/subsetP=> Hbc; apply/subsetP=> x Hx; auto.
Qed.

Lemma subset_all : forall (s : seq d) a, subset s a = all a s.
Proof. by move=> s a; exact (sameP (subsetP _ _) allP). Qed.

Lemma disjoint_sym : forall a b, disjoint a b = disjoint b a.
Proof. by move=> a b; congr eqn; apply: eq_card => x; apply: andbC. Qed.

Lemma eq_disjoint : forall a a', a =1 a' -> disjoint a =1 disjoint a'.
Proof. by move=> a a' Ea b; congr eqn; apply: eq_card => x; congr andb. Qed.

Lemma disjoint_subset : forall a b, disjoint a b = subset a (setC b).
Proof.
move=> a b; rewrite /subset; rewrite 2!(disjoint_sym a).
by apply: eq_disjoint => x; rewrite /setC negb_elim.
Qed.

Lemma disjoint_trans : forall a b c, subset a b -> disjoint b c -> disjoint a c.
Proof. move=> a b c; rewrite 2!disjoint_subset; apply subset_trans. Qed.

Lemma disjoint0 : forall a, disjoint set0 a.
Proof. by move=> a; apply/(set0P _). Qed.

Lemma disjoint1 : forall x a, disjoint (set1 x) a = ~~ a x.
Proof.
move=> x a; apply negb_sym; apply: (sameP _ (set0Pn (setI (set1 x) a))).
rewrite /setI; apply: introP=> Hx; first by exists x; rewrite set11.
by case=> y; case/andP=> [Dx Hy]; case: (negP Hx); rewrite (eqP Dx).
Qed.

Lemma disjointU : forall a a' b,
  disjoint (setU a a') b = disjoint a b && disjoint a' b.
Proof.
move=> a a' b; rewrite /disjoint; case: (set0P (setI a b)) => [Hb|Hb] /=.
congr eqn; apply: eq_card => x; move: {Hb}(Hb x); rewrite /setI /setU.
  by case (b x); [ rewrite andbT; move -> | rewrite !andbF ].
apply/(set0P _) => [Ha]; case: Hb => x; apply/nandP.
case/nandP: {Ha}(Ha x); auto; case/norP; auto.
Qed.

Lemma disjointU1 : forall x a b,
  disjoint (setU1 x a) b = ~~ b x && disjoint a b.
Proof.
by move=> x a b; rewrite -(@eq_disjoint (setU (set1 x) a)) ?disjointU ?disjoint1.
Qed.

Lemma disjoint_has : forall (s : seq d) a, disjoint s a = ~~ has a s.
Proof.
move=> s a; rewrite has_count -(eq_count (filter_enum a)) -has_count has_sym.
by rewrite has_count count_filter -filter_setI -count_filter -leqNgt leqn0.
Qed.

Lemma disjoint_cat : forall s1 s2 a,
  disjoint (cat s1 s2) a = disjoint s1 a && disjoint s2 a.
Proof. by move=> *; rewrite !disjoint_has has_cat negb_orb. Qed.

End FiniteSet.

Prenex Implicits card set0b pick subset disjoint.

Implicit Arguments card_uniqP [d s].
Implicit Arguments subsetP [d a b].
Implicit Arguments set0P [d a].
Implicit Arguments set0Pn [d a].
Implicit Arguments subset_eqP [d a b].
Prenex Implicits card_uniqP subsetP set0P set0Pn subset_eqP.

(* setType BEGIN *)

Section PermGen.

Variable d : finType.

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

Lemma uniq_mkpermr : forall m, uniq (mkpermr m).
Proof.
elim=> //= i IHi; elim: enum (uniq_enum d) => //= x e IHe.
move/andP=> [Hx He]; rewrite uniq_cat {}IHe {He}// andbT.
rewrite {1}/multes uniq_maps ?{}IHi; last move=> _ _ [] //.
apply/hasP; case=> s Hs.
by move/mapsP => [s' _ Ds]; rewrite mem_multss -Ds (negbET Hx) in Hs.
Qed.

End PermGen.


Section FinGraphEqT.
Variables (d1 :finType) (d2 : eqType).

CoInductive fgraphType : Type := 
  Fgraph (val:seq d2) : (size val) = (card (setA d1)) -> fgraphType.

Definition fval : fgraphType -> seq d2 :=
  fun x => match x with Fgraph val _ => val end.

Definition fproof : forall u, size (fval u) = (card (setA d1)) :=
  fun x => match x return size (fval x) = (card (setA d1)) with
           | Fgraph _ proof => proof end.

Lemma fgraph_eqP : reflect_eq (fun f1 f2 => fval f1 == fval f2).
Proof.
move=> [s1 Hs1] [s2 Hs2]; apply: (iffP eqP) => [/= Hs1s2|-> //].
by rewrite Hs1s2 in Hs1 |- *; rewrite /= (nat_irrelevance Hs1 Hs2).
Qed.

Canonical Structure fgraph_eqType := EqType fgraph_eqP.

Lemma fval_eqE : forall u v : fgraph_eqType, (fval u == fval v) = (u == v).
Proof. done. Qed.

Lemma fval_inj : injective fval.
Proof. by move => u v; move/eqP; move/fgraph_eqP. Qed.

 (* if the domain is not empty the default is the first elem of the graph *)
Lemma fgraph_default : d1 -> fgraphType -> d2.
Proof. by move=> x [[|//]]; rewrite /card; case: enum (mem_enum x). Qed.

End FinGraphEqT.

Section FinGraph.

Variables (d1 d2:finType).

Definition infgraph (s : seq d2) : option (@fgraphType d1 d2) :=
  if size s =P (card (setA d1)) is Reflect_true Hs then Some (Fgraph Hs) else None.

CoInductive infgraph_spec (s : seq d2) : option (@fgraphType d1 d2) -> Type :=
  | Some_tup u : size s = (card (setA d1)) -> fval u = s -> infgraph_spec s (Some u)
  | None_tup: ~~ (size s == (card (setA d1))) -> infgraph_spec s None.

Lemma infgraphP : forall s, infgraph_spec s (infgraph s).
Proof. by rewrite /infgraph => s; case: eqP; [left | right; exact/eqP]. Qed.

Definition infgraphseq : seq (seq_eqType d2) -> seq (fgraph_eqType d1 d2) :=
  foldr (fun (s:seq d2) ts => if infgraph s is Some u then Adds u ts else ts) seq0.

Lemma mem_infgraphseq : forall a, infgraphseq a =1 (fun u => a (fval u)).
Proof.
elim=> // s a IHa u /=.
case: infgraphP => [v _ Dv | Hs]; rewrite /= /setU1 IHa -?Dv //.
by case: eqP => // Ds; case/eqP: Hs; rewrite Ds fproof.
Qed.

Lemma uniq_infgraphseq : forall s, uniq s -> uniq (infgraphseq s).
Proof.
elim => // e s IH Hes. 
rewrite uniq_adds in Hes;move/andP: Hes => [He Hs] /=;have:=IH Hs.
case: infgraphP => // u Hu Du Hins; rewrite uniq_adds.
by apply/andP; split => //; rewrite mem_infgraphseq Du.
Qed.

(* the sequence of all the n-tuples on the d alphabet *)
Definition finfgraph_enum := infgraphseq (mkpermr d2 (card (setA d1))).

Lemma maps_tval_fintuple_enum: 
  maps (@fval d1 d2) finfgraph_enum = mkpermr d2 (card (setA d1)).
Proof.
rewrite /finfgraph_enum.
have: all (fun s => size s == (card (setA d1))) (mkpermr d2 (card (setA d1))).
  by apply/allP => s; rewrite mem_mkpermr_size.
elim: (mkpermr d2 (card (setA d1))) => //= s s2 IHs; move/andP => [Hs Hs2].
by case: infgraphP => [_ _ /= ->|]; [rewrite (IHs Hs2)|rewrite Hs].
Qed.

  (* good enumeration *)
Lemma finfgraph_enumP : forall u, count (set1 u) finfgraph_enum = 1.
Proof.
move => [s ps]. 
rewrite /finfgraph_enum count_set1_uniq; last exact (uniq_infgraphseq (uniq_mkpermr d2 (card (setA d1)))).
by rewrite mem_infgraphseq /= mem_mkpermr_size ps set11.
Qed.

Canonical Structure fgraph_finType := FinType finfgraph_enumP.

End FinGraph.

Definition fgraph_of_fun := 
  locked (fun (d1 :finType) (d2 :eqType) (f : d1 -> d2) => Fgraph (size_maps f _)).

Definition fun_of_fgraph := 
  locked 
   (fun d1 (d2:eqType) g x => 
      sub (@fgraph_default d1 d2 x g) (fval g) (index x (enum d1))).

Coercion fun_of_fgraph : fgraphType >-> Funclass.

Lemma can_fun_of_fgraph : forall (d1 : finType) (d2 : eqType),
  cancel (@fun_of_fgraph d1 d2) (@fgraph_of_fun d1 d2).
Proof.
unlock fun_of_fgraph => d1 d2 g.
case: {-1}g => [s Hs]; unlock fgraph_of_fun; apply fval_inj => /=.  
case De: (enum _) => [|x0 e]; first by case: s Hs; rewrite /card De. 
rewrite -De; have y0 := fgraph_default x0 g.
apply: (@eq_from_sub _ y0); rewrite size_maps // => i Hi; unlock.
by rewrite (sub_maps x0) // index_uniq ?uniq_enum ?(set_sub_default y0) ?Hs.
Qed.

Lemma g2f : 
  forall (d1 :finType) (d2 :eqType) (f:d1->d2), fgraph_of_fun f =1 f.
Proof.
unlock fun_of_fgraph fgraph_of_fun => /= d1 d2 f x.
by rewrite (sub_maps x) ?sub_index // ?index_mem mem_enum.
Qed.

Lemma fgraphP : forall (d1 : finType) (d2 :eqType) (f g : fgraphType d1 d2), f =1 g <-> f = g.
Proof.
move=> d1 d2 f g; split; last by move=>->. 
move=> Efg; rewrite -(can_fun_of_fgraph f) -(can_fun_of_fgraph g).
by apply: fval_inj; unlock fgraph_of_fun => /=; apply: eq_maps.
Qed.

Lemma fgraph_size : forall T1 T2 (a b:fgraphType T1 T2),
  size (fval a) = size (fval b).
Proof. by move => T1 T2 a b; case a; case b => sa Hsa sb Hsb /=; rewrite Hsa Hsb.
Qed.

Lemma can_eq: forall d : eqType, forall d1 : Type, forall f f1, 
  cancel f f1 -> reflect_eq (fun (x y : d1) => f x == f y :> d).
Proof.
move => d d1 f f1 Hf x y; apply: (iffP eqP).
  by apply: (can_inj Hf).
by apply: f_equal.
Qed.

Definition uniqmap := locked (fun (d : finType) (d1 : eqType) (f:d -> d1) =>
                        (undup (maps f (enum d)))).

Lemma can_uniq:
 forall d : finType, forall d1 : eqType, forall f f1, cancel f1 f ->
 forall u : d1, count (set1 u) (@uniqmap d d1 f) = 1.
Proof.
move => d d1 f f1 Hf1 u; unlock uniqmap.
rewrite count_set1_uniq ?uniq_undup // mem_undup -[u]Hf1 (_ : maps _ _ _ = true) //.
by apply/mapsP; exists (f1 u); first exact: mem_enum.
Qed.


Section SetType.

Variable G : finType.

CoInductive setType : Type := Sett : fgraphType G bool_finType -> setType.

Definition sval (s : setType) := match s with Sett g => g end.

Lemma can_sval : cancel sval Sett.
Proof. by rewrite /cancel; case => /=. Qed.

Lemma sval_inj : injective sval. 
Proof. exact: can_inj can_sval. Qed.

Canonical Structure set_eqType := EqType (can_eq can_sval). 

Canonical Structure set_finType := FinType (can_uniq can_sval).

Definition iset_of_fun (f : G -> bool_finType) : setType := 
  locked Sett (fgraph_of_fun f).

Definition s2s : setType -> set G := 
  fun s => @fun_of_fgraph G bool_finType (sval s).

Coercion s2s : setType >-> set.

Lemma can_iset_of_fun : forall f, iset_of_fun f =1 f.
Proof. 
move => f; rewrite /s2s /iset_of_fun; unlock => /=; exact: g2f.
Qed.

Definition s2f := can_iset_of_fun.

End SetType.

Notation "{ x , P }" := (iset_of_fun (fun x => P)) (at level 0, x at level 99).
Notation "{ x : T , P }" := (iset_of_fun (fun x : T => P)) (at level 0, x at level 99).

Lemma isetP : forall (G : finType) (a b : setType G), a =1 b <-> a = b.
Proof.
by move => G a b; split => H; [apply: sval_inj | rewrite H]; apply/fgraphP.
Qed.

Section setTypeOpsDefs.

Variable G : finType.

Definition iset1 x : setType G := {y, x==y}.
Definition iset2 x1 x2 : setType G := {y, (x1 == y) || (x2 == y)}.
Definition iset3 x1 x2 x3 : setType G := {y, or3b (x1 == y) (x2 == y) (x3 == y)}.
Definition iset4 x1 x2 x3 x4 : setType G :=
  {y, or4b (x1 == y) (x2 == y) (x3 == y) (x4 == y)}.
Definition isetU (A B:setType G) : setType G := {x, A x || B x}.
Definition isetU1 x A : setType G := {y, (x == y) || A y}.
Definition isetI (A B : setType G): setType G := {x, A x && B x}.
Definition isetC (A:setType G) : setType G := {x, ~~ A x}.
Definition isetC1 x : setType G:= {y, x != y}.
Definition isetD (A B:setType G) : setType G := {x, ~~ B x && A x}.
Definition isetD1 (A:setType G) x : setType G := {y, (x != y) && A y}.
Definition iset0 := {x : G, false}.
Definition isetA := {x : G, true}.

End setTypeOpsDefs.

Coercion isetA : finType >-> setType.

Notation "A ':|' x" := (isetU1 x A) (at level 52, left associativity).
Notation "A ':|:' B" := (isetU A B) (at level 52, left associativity).
Notation "A ':\:' B" := (isetD A B) (at level 50).
Notation "A ':\' x" := (isetD1 A x) (at level 50).
Notation "A ':&:' B" := (isetI A B) (at level 48, left associativity).
Notation "'{:' x }" := (iset1 x) (at level 0, x at level 99, format"'{:' x }").
Notation "'~:' A" := (isetC A) (at level 35).
Notation "'{~:' x }" := (isetC1 x) (at level 0, x at level 99). 
Notation "'{:' x , y }" := (iset2 x y) (at level 0, x at level 99, y at level 99).  

Lemma isetAP : forall (G : finType) x, G x.
Proof. by move=> G x; rewrite s2f. Qed.

Hint Resolve isetAP.

Section setTypeOps.

Variable G : finType.

Lemma iset1P : forall x y:G, reflect (x = y) ({:x} y).
Proof. move=> x y; rewrite s2f; exact:eqP. Qed.

Lemma iset11 : forall x:G, {: x} x. 
Proof. move=> x; rewrite s2f; exact: eq_refl. Qed.

Lemma isetU11 : forall (x:G) a, (a :| x) x.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma isetU1r : forall (x:G) a, sub_set a (a :| x).
Proof. by move=> x a y Hy; rewrite s2f Hy orbT. Qed.

Lemma isetU1P : forall x (a : setType G) y, reflect (x = y \/ a y) ((a :| x) y).
Proof.
by move=>*;rewrite s2f;apply:(iffP orP);case;auto;left;[apply:eqP|apply/eqP].
Qed.

Lemma isetC11 : forall x:G, {~:x} x = false.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma isetD11 : forall (x:G) a, (a :\ x) x = false.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma iset21 : forall (x1 x2:setType G), {:x1,x2} x1.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma iset22 : forall (x1 x2:setType G), {:x1,x2} x2.
Proof. by move=> *; rewrite s2f eq_refl orbT. Qed.

Lemma iset31 : forall (x1 x2 x3:setType G), iset3 x1 x2 x3 x1.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma iset32 : forall (x1 x2 x3:setType G), iset3 x1 x2 x3 x2.
Proof. by move=> *; rewrite s2f eq_refl !orbT . Qed.

Lemma iset33 : forall (x1 x2 x3:setType G), iset3 x1 x2 x3 x3.
Proof. by move=> *; rewrite s2f eq_refl !orbT. Qed.

Lemma isetIUr : forall b1 b2 b3 : setType G, 
  b1 :&: (b2 :|: b3) = (b1 :&: b2) :|: (b1 :&: b3).
Proof. move => a b c; apply/isetP => x; rewrite !s2f; exact: demorgan1. Qed.

Lemma isetIUl : forall b1 b2 b3:setType G,
  (b1 :|: b2) :&: b3 = (b1 :&: b3) :|: (b2 :&: b3).
Proof. move => a b c; apply/isetP => x; rewrite !s2f; exact: demorgan2. Qed.

Lemma isetUIr : forall b1 b2 b3:setType G, 
  b1 :|: (b2 :&: b3) = (b1 :|: b2) :&: (b1 :|: b3).
Proof. move => a b c; apply/isetP => x; rewrite !s2f; exact: demorgan3. Qed.

Lemma isetUIl : forall b1 b2 b3:setType G, 
  (b1 :&: b2) :|: b3 = (b1 :|: b3) :&: (b2 :|: b3).
Proof. move => a b c; apply/isetP => x; rewrite !s2f; exact: demorgan4. Qed.

Lemma isetCI : forall b1 b2:setType G,
  ~: (b1 :&: b2) = ~:b1 :|: ~:b2.
Proof. 
by move => a b; apply/isetP => x; rewrite !s2f; apply/idP/idP;
  [move/nandP => H; apply/orP|move => H; apply/nandP; apply/orP].
Qed.

Lemma isetUs : forall a b1 b2 : setType G,
  subset b1 b2 -> subset (a :|: b1) (a :|: b2).
Proof.
move => a b1 b2; move/subsetP => sb12; apply/subsetP=>x.
rewrite !s2f; case: (a x) => H; apply/orP; [left|right] => //.
rewrite orFb in H; exact: (sb12 x H).
Qed.

Lemma isetsU : forall a b1 b2 : setType G,
  subset b1 b2 -> subset (b1 :|: a) (b2 :|: a).
Proof.
move => a b1 b2; move/subsetP => sb12; apply/subsetP=>x.
rewrite !s2f; case: (a x) => H; apply/orP; [right|left] => //.
rewrite orbF in H; exact: (sb12 x H).
Qed.

Lemma isetIA: forall A B C: setType G, A :&: B :&: C = A :&: (B :&: C).
Proof. by move=> A B C; apply/isetP=> x; rewrite !s2f andbA. Qed.

Lemma isetUA : forall a b c : setType G,
  a :|: (b :|: c) = a :|: b :|: c.
Proof.
move => a b c; apply/isetP => x;rewrite !s2f.
by case: (a x); case: (b x); case: (c x).
Qed.

Lemma isetIP : forall x (a b : setType G), reflect (a x /\ b x) ((a :&: b) x).
Proof. move => x a b; rewrite !s2f; exact: andP. Qed.

Lemma isetUP : forall x (a b : setType G), reflect (a x \/ b x) ((a :|: b) x).
Proof. move => x a b; rewrite !s2f; exact: orP. Qed.

Lemma isetCP : forall x (a : setType G), reflect (~ a x) ((~:a) x).
Proof. move => x a; rewrite !s2f; exact: negP. Qed.

Lemma isetIC : forall a b:setType G, a :&: ~:b = a :\: b.
Proof. by move => a b; apply/isetP => x; rewrite !s2f andbC. Qed.

Lemma isetDU : forall a b c : setType G, a :\: (b :|: c) = (a :\: b) :&: (a :\: c).
Proof.
move => a b c; apply/isetP=>x;rewrite !s2f.
by case: (a x); case: (b x); case: (c x).
Qed.

Lemma isetDI : forall a b c : setType G, a :\: (b :&: c) = (a :\: b) :|: (a :\: c).
Proof.
move => a b c; apply/isetP=>x;rewrite !s2f.
by case: (a x); case: (b x); case: (c x).
Qed.

Lemma isetC_inj: forall a b:setType G, ~: a = ~: b -> a = b.
Proof.
move => a b; apply: (@can_inj _ _ _ (@isetC G)); rewrite /cancel => c.
by apply/isetP => x;rewrite !s2f; case: (c x). 
Qed.

Lemma isetCU : forall b1 b2:setType G,
  ~: b1 :&: ~: b2 = ~: (b1 :|: b2).
Proof. 
by move => a b; apply/isetP => x; rewrite !s2f; apply/idP/idP;
  [move => H; apply/norP; apply/andP|move/norP => H; apply/andP].
Qed.

Lemma icard1 : forall x:G, card {:x} = 1.
Proof.
move => x; rewrite /card /iset1 -(@eq_count _ (set1 x)); 
  [exact: FinType.enumP | by move => y; rewrite s2f].
Qed.

Lemma icardUI : forall a b:setType G, card (a :|: b) + card (a :&: b) = card a + card b.
Proof. move=> a b. 
rewrite -(@eq_card _ (setU a b)); last by move=>y;rewrite s2f.
rewrite -[card (isetI _ _)](@eq_card _ (setI a b)); last by move=>y;rewrite s2f.
exact: count_setUI. 
Qed.

Lemma icard0 : card (iset0 G) = 0.
Proof.
case: (pickP (iset0 G)); first by move => x; rewrite s2f.
move => H; rewrite (eq_card H).
exact: card0.
Qed.

Lemma icardIC : forall b a:setType G, card (a :&: b) + card (a :&: ~:b) = card a.
Proof.
move=> b a; rewrite -(add0n (card a)) -icardUI addnC -icard0.
by congr (_ + _); apply: eq_card => x; rewrite !s2f;
   case (a x); case (b x).
Qed.

Lemma icardC : forall a:setType G, card a + card (~:a) = card (setA G).
Proof. move=> a. 
rewrite (cardA G) -(count_setC a) -[card (isetC _)](@eq_card _ (setC a)) //.
by move=>y; rewrite s2f.
Qed.

Lemma icardU1 : forall (x:G) a, card (a :| x) = ~~ (a x) + card a.
Proof.
move => x a; rewrite -(@eq_card _ (setU1 x a)); last by move=>y; rewrite s2f.
apply: addn_injr (etrans (cardUI _ _) _); symmetry.
rewrite addnC addnA; congr addn; rewrite -(@eq_card _ (filter a (Seq x))).
  simpl; case: (a x); last by rewrite /= card0 card1.
  by rewrite addnC; apply: eq_card => y; exact: mem_seq1.
by move=> y; rewrite mem_filter /setI mem_seq1 andbC.
Qed.

Lemma icard2 : forall x y:G, card {:x, y} = S (x != y).
Proof.
move=> x y /=; rewrite -(@eq_card _ (set2 x y)); last by move=>z;rewrite s2f.
by apply: (etrans (cardU1 x (set1 y))); rewrite card1 addn1 eq_sym.
Qed.

Lemma icardC1 : forall x:G, card {~:x} = pred (card (setA G)).
Proof. 
move=> x; rewrite -(icardC (iset1 x)) icard1.
by apply: eq_card; move => y; rewrite !s2f.
Qed.

Lemma icardD1 : forall x (a:setType G), card a = a x + card (a :\ x).
Proof.
move=> x a; rewrite -(@eq_card _ (setD1 a x) (isetD1 _ _)); last by move=>y;rewrite s2f.
rewrite addnC; apply: (addn_injr (etrans (cardC a) _)).
rewrite -addnA (negb_intro (a x)) -[negb (a x)]/(setC a x) -cardU1.
symmetry; apply: etrans (congr1 (addn _) _) (cardC _).
by apply: eq_card => y; rewrite /setC /setU1 /setD1 negb_andb negb_elim.
Qed.

Lemma icard0_eq : forall (a:setType G), card a = 0 -> a = (iset0 G).
Proof. 
by move=> a Ha; apply/isetP=>x; rewrite s2f; apply/idP => [Hx]; rewrite (icardD1 x) Hx in Ha. 
Qed.

Lemma icard_card : forall s, card {x:G,s x} = card s.
Proof. by move=> s; apply:eq_card=>x; rewrite s2f. Qed.

Lemma subsetIl : forall (A B : setType G), subset (A :&: B) A.
Proof.
by move=> A B; apply/subsetP=> x; rewrite s2f; case/andP.
Qed.

Lemma subsetIr : forall (A B : setType G), subset (A :&: B) B.
Proof.
by move=> A B; apply/subsetP=> x; rewrite s2f; case/andP.
Qed. 

Lemma subsetUl : forall (A B : setType G), subset A (A :|: B).
Proof. by move=> A B; apply/subsetP=> x; rewrite s2f => ->. Qed.

Lemma subsetUr : forall (A B : setType G), subset B (A :|: B).
Proof. by move=> A B; apply/subsetP=> x; rewrite s2f orbC => ->. Qed.


Lemma subset_set1 : forall (A : setType G) x, subset {:x} A = A x.
Proof.
move=> A x; apply/subsetP/idP.
by move=> xA; apply xA; rewrite s2f set11.
by move=> Ax x'; rewrite s2f; move/eqP<-.
Qed.

End setTypeOps.


Section FunImage.

Variables (d : finType) (d' : eqType) .

Definition codom (f : d -> d') : set d' := fun x' => ~~ set0b (preimage f (set1 x')).

Remark Hiinv : forall (f : d -> d') x', codom f x' -> {x : d | x' == f x}.
Proof.
move=> f x' Hx'; pose a := x' == f _.
case: (pickP a) => [x Dx | Hnx']; first by exists x.
by rewrite /codom /preimage -/a (introT set0P Hnx') in Hx'.
Qed.

Definition iinv (f : d -> d') x' (Hx' : codom f x') := let (x, _) := Hiinv Hx' in x.

Lemma codom_f : forall (f : d -> d') x, codom f (f x).
Proof. move=> f x; apply/set0Pn; exists x; apply: set11. Qed.

Lemma f_iinv : forall (f : d -> d') x' (Hx' : codom f x'), f (iinv Hx') = x'.
Proof.
by move=> f x' Hx'; rewrite /iinv; case: (Hiinv Hx') => [x]; case/eqP.
Qed.


Lemma iinv_f : forall (f : d -> d') x (Hfx : codom f (f x)), injective f -> iinv Hfx = x.
Proof. move=> f x Hfx Hf; apply Hf; apply f_iinv. Qed.

Lemma preimage_iinv : forall (f : d -> d') a' x' (Hx' : codom f x'),
  preimage f a' (iinv Hx') = a' x'.
Proof. by move=> *; rewrite /preimage f_iinv. Qed.

Section Image.

Variable (f : d -> d') (a : set d).

Definition image : set d' := fun x' => ~~ disjoint (preimage f (set1 x')) a.

Lemma imageP : forall y,
  reflect (exists2 x, a x & y = f x) (image y).
Proof.
move=> y; apply:(iffP set0Pn) => [[x Hx]| [x Hx ->]].
 case/andP : Hx; move/eqP; by exists x.
by exists x; rewrite /setI /preimage eq_refl.
Qed.

Remark Hdiinv : forall x', image x' -> {x : d | (x' == f x) && a x}.
Proof.
move=> x' Hx'; pose b := fun x => (x' == f x) && a x.
case: (pickP b) => [x Dx | Hnx']; first by exists x.
by case/negP: Hx'; apply /set0P.
Qed.

Definition diinv x' (Hx' : image x') := let (x, _) := Hdiinv Hx' in x.

Lemma f_diinv : forall x' (Hx' : image x'), f (diinv Hx') = x'.
Proof.
move=> x' Hx'; rewrite /diinv.
by case: (Hdiinv Hx') => [x]; move/andP => [H1 _]; case/eqP: H1.
Qed.

Lemma a_diinv : forall x' (Hx' : image x'), a (diinv Hx').
Proof.
move=> x' Hx'; rewrite /diinv.
by case: (Hdiinv Hx') => [x]; move/andP => [_ H2].
Qed.

Hypothesis Hf : injective f.
Hypothesis Hfd : dinjective a f.

Lemma diinv_f : forall x (Hfx : image (f x)), a x -> diinv Hfx = x.
Proof. 
move=> x Hfx Ha; apply Hfd => //; first exact: a_diinv.
apply: f_diinv. 
Qed.

Lemma preimage_diinv : forall a' x' (Hx' : image x'),
  preimage f a' (diinv Hx') = a' x'.
Proof. by move=> *; rewrite /preimage f_diinv. Qed.


(* This first lemma does not depend on Hf : (injective f). *)
Lemma image_codom : forall x', image x' -> codom f x'.
Proof.
move=> x'; case/set0Pn=> x; case/andP; move/eqP=> Dx _; rewrite Dx.
apply codom_f.
Qed.

Lemma image_f : forall x, image (f x) = a x.
Proof.
move=> x; apply/set0Pn/idP => [[y Hy]|Hx].
  by move/andP: Hy => [Dx Hy]; rewrite (Hf (eqP Dx)).
by exists x; rewrite /setI /preimage set11.
Qed.

Lemma image_f_imp : forall x, a x -> image (f x).
Proof.
move => x H; apply/set0Pn.
by exists x; rewrite /setI /preimage eq_refl.
Qed.

Lemma image_iinv : forall x' (Hx' : codom f x'), image x' = a (iinv Hx').
Proof. by move=> x' Hx'; rewrite -image_f f_iinv. Qed.

Lemma pre_image : preimage f image =1 a.
Proof. by move=> x; rewrite /preimage image_f. Qed.

End Image.

Lemma image_set0 : forall (f : d -> d'), image f set0 =1 set0.
by move=> f x; case E: (image f set0 x) => //; move/imageP: E=> [y H _].
Qed.

Lemma image_pre : forall (f : d -> d') a',
  injective f -> image f (preimage f a') =1 setI a' (codom f).
Proof.
move=> f a' Hf x'; rewrite /setI andbC; case Hx': (codom f x'); simpl.
  by rewrite -(f_iinv Hx') image_f /preimage.
apply/idPn => [Hax']; case/idPn: Hx'; exact (image_codom Hax').
Qed.

Fixpoint preimage_seq (f : d->d') (s : seq d') : seq d :=
  if s is Adds x s' then
    (if pick (preimage f (set1 x)) is Some y then Adds y else id) (preimage_seq f s')
  else seq0.

Lemma maps_preimage : forall (f : d -> d') (s : seq d'),
  sub_set s (codom f) -> maps f (preimage_seq f s) = s.
Proof.
move=> f; elim=> [|x s Hrec] //=; case: pickP => [y Dy|Hs'] Hs.
  rewrite /= (eqP Dy) Hrec // => z Hz; apply Hs; exact: setU1r.
by case/set0P: (Hs x (setU11 _ _)).
Qed.

Lemma image_eq : forall (a b:set d)(g f:d->d'), a =1 b ->
     g =1 f -> image g a =1 image f b.
Proof.
move => a b g f Ha Hg x; apply/imageP/imageP; move => [y Hin Heq].
 by exists y; [rewrite -Ha | rewrite -Hg].
by exists y; [rewrite Ha | rewrite Hg].
Qed.

End FunImage.



Prenex Implicits codom iinv image.

Definition iimage:= 
 locked (fun (G G':finType) (f:G -> G') (A : set G) => iset_of_fun (image f A) : setType G').

Definition ipreimage (d : finType) (d' : eqType) (k : d -> d') (a : set d') := 
           {x, a (k x)}.

Notation "f '@:' A" := (iimage f A) (at level 54).
Notation "f '@^-1:' A" := (ipreimage f A) (at level 54).

Section FunIimage.

Variable G G' : finType.
Variable f : G -> G'.

Lemma iimageP : forall (A : set G) y,
 reflect (exists2 x, A x & y = f x) ((f @: A) y).
Proof. move=> A y; rewrite /iimage -lock s2f; exact: imageP. Qed.


Lemma iimage_set1 : forall x, f @: {: x } = {: f x}.
Proof.
move=> x; apply/isetP => y; unlock iimage; rewrite !s2f; apply/imageP/eqP.
  by case=>x'; rewrite s2f; move/eqP->.
by exists x=> //; rewrite iset11.
Qed.

End FunIimage.

Section Ordinal.

Variable n : nat.

CoInductive ordinal : Type := Ordinal i of (i < n).

Coercion nat_of_ord x := let: Ordinal i _ := x in i.

Lemma ordinal_ltn : forall  x: ordinal, x < n.
Proof. by case. Qed.

Lemma ordinal_inj : injective nat_of_ord.
Proof.
move=> [i lt_i] [j lt_j]/= eq_ij; rewrite eq_ij in lt_i *.
congr Ordinal; exact: bool_irrelevance.
Qed.

Lemma ord_eqP : reflect_eq (fun x y : ordinal => x == y :> nat).
Proof.
move=> [x Hx] [y Hy]; apply: (iffP eqP); [exact: ordinal_inj | by case].
Qed.

Canonical Structure ordinal_eqType := EqType ord_eqP.

Definition ord_of_natsig u := let: EqSig i lt_i := u in @Ordinal i lt_i.

Definition ord_enum :=
  maps ord_of_natsig (subfilter (fun m => m < n) (iota 0 n)).

Lemma ord_enumP : forall x, count (set1 x) ord_enum = 1.
Proof.
have injsig: injective ord_of_natsig.
  move=> [i lt_i] [j lt_j] [eq_ij]; exact: val_inj.
move=> [i lt_i]; rewrite count_set1_uniq /ord_enum.
  rewrite (mem_maps _ _ (EqSig (fun m => m < n) i lt_i)) //.
  by rewrite mem_subfilter /preimage /setI /= mem_iota /= andbC andbb lt_i.
rewrite uniq_maps //; apply: uniq_subfilter; exact: uniq_iota.
Qed.

Canonical Structure ordinal_finType := FinType ord_enumP.

Lemma card_ordinal : card (setA ordinal_finType) = n.
Proof.
rewrite cardA -(size_iota 0 n) /= /ord_enum size_maps size_subfilter.
by apply/eqP; rewrite -all_count; apply/allP=> p; rewrite mem_iota.
Qed.

End Ordinal.

(* Notation for odinal Type *)

Notation "'I_' ( n )" := (ordinal_finType n)
  (at level 0, format "'I_' ( n )").
Notation "'F_' ( n )" := (fgraphType I_(n) I_(n))
  (at level 0, format "'F_' ( n )").

Section OrdinalProp.

(* Definition ord0 : ordinal 1 := Ordinal (ltnSn 0). *)

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

Lemma lift_subproof : forall n h (i : I_(n.-1)), bump h i < n.
Proof.
by case=> [|n] h [i //= Hi]; rewrite /bump; case: (h <= _); last exact: ltnW.
Qed.

Definition lift n (h : I_(n)) (i : I_(n.-1)) :=
  Ordinal (lift_subproof h i).

Lemma unlift_subproof : forall n (h : I_(n)) (u : eq_sig (setC1 h)),
  unbump h (val u) < pred n.
Proof.
move=> n h [i] /=; move/unbumpK => Di.
have lti: (i < n) by case i.
rewrite -ltnS (ltnSpred lti).
move: lti; rewrite -{1}Di; move: {i Di} (unbump _ _) => m.
rewrite /bump; case: (leqP _ m) => // Hm _.
apply: (@leq_trans (h.+1) _ _) => //.
by case: h Hm.
Qed.

Definition unlift n (h i : I_(n)) :=
  if insub (setC1 h) i is Some u then
    Some (Ordinal (unlift_subproof u))
  else None.

CoInductive unlift_spec n (h i : I_(n)) : option I_(n.-1) -> Type :=
  | UnliftSome j of i = lift h j : unlift_spec h i (Some j)
  | UnliftNone   of i = h        : unlift_spec h i None.

Lemma unliftP : forall n (h i : I_(n)), unlift_spec h i (unlift h i).
Proof.
move=> n h i; rewrite /unlift; case: insubP => [u Hi Di | Di].
  apply: UnliftSome; 
  by apply: ordinal_inj; rewrite /= Di (unbumpK Hi).
apply: UnliftNone; by rewrite negbK in Di; move/eqP: Di.
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
move=> n h i1 i2; move/ord_eqP => //=.
by rewrite (eqtype.can_eq (@bumpK _)); move/ord_eqP.
Qed.

Lemma liftK : forall n (h : I_(n)) i, unlift h (lift h i) = Some i.
Proof.
by move=> n h i; case: (unlift_some (neq_lift h i)) => j; move/lift_inj->.
Qed.

(* Shifting and splitting indices, for cutting and pasting arrays *)

Lemma lshiftSn_subproof : forall n (i : I_(n)), i < n.+1.
Proof.
by move=> n i; apply: (@ltn_trans n) =>//; rewrite ordinal_ltn.
Qed.

Definition lshiftSn n (i : I_(n)) := Ordinal (lshiftSn_subproof i).

Lemma rshiftSn_subproof : forall n (i : I_(n)), i.+1 < n.+1.
Proof. by move=> n [i Hi]. Qed.

Definition rshiftSn n (i : I_(n)) := Ordinal (rshiftSn_subproof i).

Lemma lshift_subproof : forall m n (i : I_(m)), i < m + n.
Proof. move=> m n i; apply: (@leq_trans m _ _); [by case i| exact: leq_addr]. Qed.

Lemma rshift_subproof : forall m n (i : I_(n)), m + i < m + n.
Proof. by move=> m n i; rewrite ltn_add2l ordinal_ltn. Qed.

Definition lshift m n (i : I_(m)) := Ordinal (lshift_subproof n i).
Definition rshift m n (i : I_(n)) := Ordinal (rshift_subproof m i).

Lemma split_subproof : forall m n (i : I_(m + n)),
  i >= m -> i - m < n.
Proof. by move=> m n i; move/leq_subS <-; rewrite leq_sub_add ordinal_ltn. Qed.

Definition split m n (i : I_(m + n)) : I_(m) + I_(n) :=
  match ltnP (i) m with
  | LtnNotGeq Hi =>  inl _ (Ordinal Hi)
  | GeqNotLtn Hi =>  inr _ (Ordinal (split_subproof Hi))
  end.

CoInductive split_spec m n (i : I_(m + n)) : I_(m) + I_(n) -> bool -> Type :=
  | SplitLo (j : I_(m)) & (i = j :> nat)     : split_spec i (inl _ j) true
  | SplitHi (k : I_(n)) & (i = m + k :> nat) : split_spec i (inr _ k) false.

Lemma splitP : forall m n i, @split_spec m n i (split i) (i < m).
Proof.
rewrite /split {-3}/leq => m n i; case: (@ltnP i m) => Hi //=; first exact: SplitLo.
by apply: SplitHi; rewrite /= leq_add_sub.
Qed.

Definition unsplit m n (si : I_(m) + I_(n)) :=
  match si with inl i => lshift n i | inr i => rshift m i end.

Coercion isleft A B (u : A + B) := if u is inl _ then true else false.

Lemma ltn_unsplit : forall m n si, @unsplit m n si < m = si.
Proof. by move=> m n [] i /=; rewrite ?(ordinal_ltn i) // ltnNge leq_addr. Qed.

Lemma splitK : forall m n, cancel (@split m n) (@unsplit m n).
Proof. by move=> m n i; apply: ordinal_inj; case: splitP. Qed.

Lemma unsplitK : forall m n, cancel (@unsplit m n) (@split m n).
Proof.
move=> m n si.
case: splitP (ltn_unsplit si); case: si => //= i j; last move/addn_injl;
  by move/ordinal_inj->.
Qed.

Definition ltn_ord := ordinal_ltn.

Variable n : nat.

Definition ord0 := Ordinal (ltn0Sn n).

Definition ord_max := Ordinal (ltnSn n).

Lemma leq_ord : forall i : ordinal n.+1, i <= n.
Proof. exact: ltn_ord. Qed.

Lemma sub_ordK : forall i : ordinal n.+1, n - (n - i) = i.
Proof. move=> i; apply: leq_sub_sub; exact: leq_ord. Qed.

Definition ord_sub i := Ordinal (leq_subr i n : n - i < n.+1).

Definition ord_opp (i : ordinal n.+1) := ord_sub i.

Lemma ord_oppK : involutive ord_opp.
Proof. move=> i; apply: ordinal_inj; exact: sub_ordK. Qed.

Definition widen_ord m (le_n_m : n <= m) i :=
  Ordinal (leq_trans (ltn_ord i) le_n_m).

Definition inord i := locked ord_sub (n - i).

Lemma inord_eq : forall i, i <= n -> inord i = i :> nat.
Proof. by unlock inord => i; exact: leq_sub_sub. Qed.

Lemma inord_id : forall i : ordinal n.+1, inord i = i.
Proof. by case=> i le_i_n; apply: ordinal_inj; apply: inord_eq. Qed.

End OrdinalProp.

Implicit Arguments ord0 [n].
Implicit Arguments ord_max [n].
Implicit Arguments inord [n].

Prenex Implicits ord_opp.


Section SubFinType.

Variables (d : finType) (a : set d).

Definition sub_enum := subfilter a (enum d).

Lemma sub_enumP : forall u, count (set1 u) sub_enum = 1.
Proof.
move=> [x Hx]; rewrite count_set1_uniq /= /sub_enum.
  by rewrite mem_subfilter /preimage /setI /= mem_enum Hx.
apply: uniq_subfilter; exact: uniq_enum.
Qed.

Canonical Structure sub_finType := FinType sub_enumP.

Lemma card_sub : card (setA sub_finType) = card a.
Proof. by rewrite cardA /= /sub_enum size_subfilter. Qed.

Lemma eq_card_sub : forall b, b =1 (setA sub_finType) -> card b = card a.
Proof. by have:= eq_card_trans card_sub. Qed.

End SubFinType.

Section ProdFinType.

Variable d1 d2 : finType.

Definition prod_enum :=
  foldr (fun x1 => cat (maps (pair x1) (enum d2))) seq0 (enum d1).

Lemma prod_enumP : forall u, count (set1 u) prod_enum = 1.
Proof.
move=> [x1 x2]; rewrite -[1]/((setA d1) x1 : nat) -mem_enum /prod_enum.
elim: (enum d1) (uniq_enum d1) => [|y1 s1 Hrec] //=; move/andP=> [Hy1 Hs1].
rewrite count_cat {Hrec Hs1}(Hrec Hs1) count_maps /setU1 /comp.
case Hx1: (y1 == x1) => /=.
  rewrite (eqP Hx1) in Hy1; rewrite (negbET Hy1) (eqP Hx1) addn0 -(card1 x2).
  by apply: eq_count => y2; rewrite {1}/set1 //= / pair_eq /= set11 andTb.
rewrite addnC -{2}(addn0 (s1 x1)) -(card0 d2); congr addn.
by apply: eq_count => y; rewrite eq_sym /set1 //= / pair_eq //= Hx1 andFb.
Qed.

Canonical Structure prod_finType := FinType prod_enumP.

Lemma card_prod : card (setA prod_finType) = card (setA d1) * card (setA d2).
Proof.
rewrite !cardA /= /prod_enum; elim: (enum d1) => [|x1 s1 IHs] //=.
by rewrite size_cat {}IHs size_maps.
Qed.

Lemma eq_card_prod : forall b, b =1 (setA prod_finType) -> card b = card (setA d1) * card (setA d2).
Proof. by have:= eq_card_trans card_prod. Qed.

Variable a1: set d1.
Variable a2: set d2.

Lemma card_prod_set : card (prod_set a1 a2) = card a1 * card a2.
Proof.
rewrite /card /= /prod_enum; elim: (enum d1) => //= x1 s1 IHs.
rewrite count_cat {}IHs count_maps /comp /prod_set /=.
by case: (a1 x1); rewrite // count_set0.
Qed.

End ProdFinType.

Section SumFinType.

Variables (index : finType) (dom_at : index -> finType).

Definition finsum_dom_at i : eqType := dom_at i.
Let d := sum_eqType finsum_dom_at.

Fixpoint sum_enum (si : seq index) : seq d :=
  if si is Adds i si' then
    cat (maps (@EqSum _ finsum_dom_at i) (enum (dom_at i))) (sum_enum si')
  else seq0.

Lemma sum_enumP : forall u, count (set1 u) (sum_enum (enum index)) = 1.
Proof.
move=> [i x]; rewrite -[1]/((setA index) i : nat) -mem_enum.
elim: (enum index) (uniq_enum index) => [|j s Hrec] //=; case/andP=> [Hj Hs].
rewrite count_cat addnC /= {Hrec Hs}[count _ _](Hrec Hs) addnC.
rewrite count_filter filter_maps size_maps /= /setU1 -count_filter.
case Hi: (j == i); rewrite /= /comp.
  rewrite (eqP Hi) in Hj; rewrite (negbET Hj) (eqP Hi) /= addn0 -(card1 x).
  apply: eq_count => y; exact: sum_eq_tagged.
rewrite addnC -{2}(addn0 (s i)) -(card0 (dom_at j)); congr addn.
by apply: eq_count => y; apply/nandP; left; rewrite /= eq_sym Hi.
Qed.

Definition sum_finType := FinType sum_enumP.

Lemma card_sum :
  card (setA sum_finType) = foldr (fun i m => card (setA (dom_at i)) + m) 0 (enum index).
Proof.
rewrite cardA /=; elim: (enum index) => //= [i s <-].
by rewrite size_cat size_maps.
Qed.

Definition eq_card_sum b := @eq_card_trans _ b _ _ card_sum.

End SumFinType.

Section BijectionCard.

Lemma can_card_leq :  forall (d d' : finType) (f : d -> d') (g : d' -> d),
  cancel f g -> card (setA d) <= card (setA d').
Proof.
move=> d d' f g Hfg; rewrite (cardA d') -(size_maps g).
apply: (leq_trans (subset_leq_card _) (card_size _)).
by apply/subsetP => x _; apply/mapsP; exists (f x); rewrite ?mem_enum.
Qed.

Lemma bij_eq_card_setA : forall d d' : finType,
  (exists f : d -> d', bijective f) -> card (setA d) = card (setA d').
Proof.
move=> d d' [f [g Hfg Hgf]]; apply: eqP.
by rewrite eqn_leq (can_card_leq Hfg) (can_card_leq Hgf).
Qed.

Lemma eq_card_setA : forall d d' : finType, d = d' :> Type -> card (setA d) = card (setA d').
Proof.
move=> d [[d' eqd' eqd'P] ed' Hed'] Hdd'; simpl in Hdd'.
case: d' / Hdd' in eqd' eqd'P ed' Hed' *.
by apply bij_eq_card_setA; do 2 exists (@id d).
Qed.

Lemma bij_eq_card : forall (d d' : finType) (a : set d) (a' : set d'),
 (exists f : sub_finType a -> sub_finType a', bijective f) -> card a = card a'.
Proof. by move=> d d' a a'; move/bij_eq_card_setA; rewrite !card_sub. Qed.

Lemma assoc_finType_default : forall d1 d2 : finType,
  card (setA d1) = card (setA d2) -> d1 -> d2.
Proof.
rewrite /card => d1 d2 Ed12 x1.
by case: (enum d2) Ed12; first case: (enum d1) (mem_enum x1).
Qed.

Definition assoc_finType d1 d2 Ed12 x1 :=
  sub (assoc_finType_default Ed12 x1) (enum d2) (index x1 (enum d1)).

Lemma assoc_finTypeK : forall d1 d2 Ed12 Ed21,
  cancel (@assoc_finType d1 d2 Ed12) (@assoc_finType d2 d1 Ed21).
Proof.
move => d1 d2 Ed12 Ed21 x; set y := assoc_finType _ x.
rewrite /assoc_finType {2}/y /assoc_finType.
rewrite index_uniq ?sub_index ?uniq_enum ?mem_enum //.
by rewrite -cardA Ed21 cardA index_mem mem_enum.
Qed.

Lemma eq_card_setA_bij : forall d1 d2 : finType,
  card (setA d1) = card (setA d2) -> {f : d1 -> d2 &  {g : d2 -> d1 | cancel f g &  cancel g f}}.
Proof.
move=> d d' E12; exists (assoc_finType E12).
exists (assoc_finType (esym E12)); exact: assoc_finTypeK.
Qed.

Lemma eq_card_bij : forall (d d' : finType) (a : set d) (a' : set d'),
 let da := sub_eqType a in let da' := sub_eqType a' in
 card a = card a' -> {f : da -> da' &  {g : da' -> da | cancel f g &  cancel g f}}.
Proof.
move=> d d' a a'; rewrite -card_sub -(card_sub a'); exact: eq_card_setA_bij.
Qed.

End BijectionCard.

Section CardFunImage.

Variables (d d' : finType) (f : d -> d').

Lemma leq_image_card : forall a, card (image f a) <= card a.
Proof.
move=> a; set p := filter a (enum d).
have Up: (uniq p) by apply: uniq_filter; apply uniq_enum.
rewrite -(eq_card (filter_enum a)) -/p (card_uniqP Up) -(size_maps f).
apply: (leq_trans (subset_leq_card _) (card_size _)); apply/subsetP => u.
case/set0Pn=> x; case/andP; move/eqP=> Du Hx.
by apply/mapsP; exists x; first by rewrite /p filter_enum.
Qed.

Hypothesis Hf : injective f.

Lemma card_image : forall a, card (image f a) = card a.
Proof.
move=> a; apply bij_eq_card.
have Hf1: forall w : sub_eqType (image f a), a (iinv (image_codom (valP w))).
  by move=> [x' Hx']; rewrite -image_iinv.
have Hf2: forall w : sub_eqType a, image f a (f (val w)).
  by move=> [x Hx]; rewrite image_f.
exists (fun w => EqSig a _ (Hf1 w)); exists (fun w => EqSig (image f a) _ (Hf2 w)).
  by move=> [x Hx]; apply: val_inj; rewrite /= f_iinv.
by move=> [x Hx]; apply: val_inj; rewrite /= iinv_f.
Qed.

Lemma card_codom : card (codom f) = card (setA d).
Proof.
apply: etrans (card_image (setA d)); apply: eq_card => x'.
apply/idPn/idP; last exact: image_codom.
by move=> Hx; rewrite -(f_iinv Hx) image_f.
Qed.

Lemma card_preimage : forall a', card (preimage f a') = card (setI (codom f) a').
Proof.
move=> a'; apply: etrans (esym (card_image _)) (eq_card _) => x'.
by rewrite (image_pre a' Hf) /setI andbC.
Qed.

Lemma card_dimage : forall (a: set d), 
(dinjective a f) -> card (image f a) = card a.
Proof.
move=> a Hfa; apply bij_eq_card.
have Hf1: forall w : sub_eqType (image f a), a (diinv (valP w)).
  by move=> [x' Hx'] /=; rewrite a_diinv.
have Hf2: forall w : sub_eqType a, image f a (f (val w)).
  by move=> [x Hx] /=; rewrite image_f_imp.
exists (fun w => EqSig a _ (Hf1 w)); exists (fun w => EqSig (image f a) _ (Hf2 w)).
  by move=> [x Hx]; apply: val_inj; rewrite /= f_diinv.
by move=> [x Hx]; apply: val_inj; rewrite /= diinv_f.
Qed.

End CardFunImage.

Section CardFunIimage.

Variables (d d' : finType) (f : d -> d').

Lemma iimage_card : forall a, card (f @: a) = card (image f a).
Proof.
by move => a; apply: eq_card => x; unlock iimage; rewrite !s2f.
Qed.

Lemma leq_iimage_card : forall a, card (f @: a) <= card a.
Proof.
move => a; rewrite iimage_card; exact: leq_image_card.
Qed.

Hypothesis Hf : injective f.

Lemma card_iimage : forall a, card (f @: a) = card a.
Proof.
move=> a; rewrite iimage_card; exact:card_image.
Qed.

Lemma card_diimage : forall (a: set d), 
(dinjective a f) -> card (f @: a) = card a.
Proof.
move=> a Hfa; rewrite iimage_card; exact: card_dimage.
Qed.

End CardFunIimage.


Section Disjoint.

Variables d: finType.
Variables d': eqType.
Variable a: set d.
Variable S:  d -> set d'.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being disjoint for indexed sets:                    *)
(*    S_i inter S_j <> 0 -> i = j                                     *)
(*                                                                    *)
(**********************************************************************)

Definition disjointn:= 
  forall u v x, a u -> a v -> S u x -> S v x -> u = v.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being weak disjoint for indexed sets                *)
(*    S_i inter S_j <> 0 -> S_i = S_j                                 *)
(*                                                                    *)
(**********************************************************************)

Definition wdisjointn:= 
  forall u v x, a u -> a v -> S u x -> S v x -> S u =1 S v.

Lemma disjointnW: disjointn -> wdisjointn.
  by move => H u v x H1 H2 H3 H4; 
     rewrite (H _ _ _ H1 H2 H3 H4) => x1.
Qed.

End Disjoint.

Section Sum.

Variables d: finType.
Variable a: set d.
Variable N:  d -> nat.

(**********************************************************************)
(*                                                                    *)
(*  Definition of the summation                                       *)
(*                                                                    *)
(**********************************************************************)

Definition sum := 
  foldr (fun z => (addn (N z))) 0 (filter a (enum d)).

End Sum.

Lemma sum0: forall (d: finType) (N: d -> nat),
  sum set0 N = 0.
Proof.
by move => d N; rewrite /sum filter_set0.
Qed.

Lemma sumD1: forall (d: finType) x (a: set d) (N: d -> nat),
  a x -> sum a N = N x + sum (setD1 a x) N.
Proof.
move => d x a N.
have F1: (setD1 a x) =1 (setD1 (filter a (enum d)) x).
  by move => x1; rewrite /setD1 filter_enum.
rewrite /sum (eq_filter F1) -(filter_enum a x).
elim: (enum d) (uniq_enum d) => [| x1 s1 Hrec] //=; rewrite /id.
case/andP; move/negP => H1 H2.
case E1: (a x1) => /=.
  case/orP => H3.
    rewrite -!(eqP H3) setD11; congr addn.
    congr foldr.
    apply: eqd_filter => x2 Hx2.
    rewrite /setD1 /setU1.
    case E2: (x1 == x2) => /=.
      by case H1; rewrite (eqP E2).
    by rewrite mem_filter /setI Hx2 andbT.
  have F2: setD1 (setU1 x1 (filter a s1)) x x1.
    rewrite mem_filter in H3; case/andP: H3 => H3 H4.
    rewrite /setD1 /setU1 mem_filter /setI.
    case E2: (x == x1) => /=; first by case H1; rewrite -(eqP E2).
    by rewrite eq_refl.
  rewrite F2 Hrec //= !addnA; congr addn; first exact: addnC.
  congr foldr.
  apply: eqd_filter => x2 Hx2.
  rewrite /setD1 /setU1.
  case E2: (x == x2) => //=; rewrite mem_filter /setI.
  case (a x2) => //=; case E3: (x1 == x2) => //=.
  by case H1; rewrite (eqP E3).
move => H3; rewrite Hrec //.
have F2: (setD1 (filter a s1) x x1) = false.
  by rewrite /setD1 mem_filter /setI E1 /= andbF.
rewrite F2.
congr addn; congr foldr.
Qed.

Lemma eq_sum: forall (d: finType) a b (N: d -> nat),
  a =1 b -> sum a N = sum b N.
move => d a b N H.
rewrite /sum; elim: (enum d) => [| x s Hrec] //=.
by rewrite H; case (b x) => //=; congr addn.
Qed.

Lemma eq_sumf: forall (d: finType) (a: set d) (N1 N2: d -> nat),
  (forall x, a x -> N1 x = N2 x) -> sum a N1 = sum a N2.
move => d a N1 N2 H.
rewrite /sum; elim: (enum d) 0 => [| x s Hrec n] //=.
case E1:(a x) => //=; congr addn => //.
rewrite H //.
Qed.

Lemma sum1: forall (d: finType) x (N: d -> nat),
  sum (set1 x) N = N x.
Proof.
move => d x N.
rewrite (@sumD1 _ x) //.
have F1: setD1 (set1 x) x =1 set0.
  by move => x1; rewrite /setD1; case (x == x1).
by rewrite (eq_sum _ F1) sum0 addn0.
Qed.

Lemma sum_id: forall (d: finType) (a: set d) N l,
  (forall x, a x -> N x = l) -> sum a N = card a * l.
Proof.
move => d a N l H.
have F1: (forall x: d, (filter a (enum d) x) -> N x = l).
  move => x; rewrite filter_enum; exact: H.
rewrite -(eq_card (filter_enum a)).
move: F1; rewrite /sum.
elim: (enum d) (uniq_enum d) => 
  [| x1 s1 Hrec] //=; rewrite /id /=; first by rewrite card0.
case/andP => Hu1 Hu2.
case E1: (a x1) => //= H1; last exact: Hrec.
have F1: forall x, filter a s1 x -> N x = l.
  by move => x Hx; apply: H1; rewrite /setU1 Hx orbT.
by rewrite Hrec // cardU1 H ?E1 // mem_filter /setI (negbET Hu1)
           andbF. 
Qed.

Lemma sum_card: forall (d: finType) a,
  card a = sum a (fun x:d => 1).
Proof.
move => d a.
rewrite -(muln1 (card a)); symmetry.
exact: sum_id.
Qed.

Lemma sum_setU: forall (d: finType) (a b: set d) (N: d -> nat),
  disjoint a b -> sum (setU a b) N =  (sum a N) + (sum b N).
move => d a b N.
elim: {a}(card a) {-2}a (refl_equal (card a)) b =>
   [| n Hrec] a Ha b Hab.
  rewrite (eq_sum _ (card0_eq Ha)) sum0.
  have F1: (setU a b) =1 b.
    by move => x; rewrite /setU (card0_eq Ha). 
  by rewrite (eq_sum _ F1).
have F1: ~~set0b a.
  by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F1 => x Hx.
rewrite (@sumD1 _ x) ?(@sumD1 _ x a) //; last by rewrite /setU Hx.
rewrite -!addnA; congr addn.
have F0: card (setD1 a x) = n.
  apply (@addn_injl 1%N).
  by rewrite (add1n n) -Ha (cardD1 x a) Hx.
have F1: setD1 (setU a b) x =1 (setU (setD1 a x) b).
  move => x1; rewrite /setD1 /setU.
  case E1: (x == x1) => //=.
  rewrite /disjoint /set0b in Hab.
  move: (card0_eq (eqP Hab)) => H1.
  case E2: (b x1) => //; case (H1 x1).
  by rewrite /setI E2 -(eqP E1) Hx.
rewrite (eq_sum _ F1) Hrec //.
rewrite /disjoint; apply/set0P => x1.
rewrite /setI /setD1.
case E1: (x == x1) => //=.
rewrite /disjoint /set0b in Hab.
case E2: (a x1) => //=.
move: (card0_eq (eqP Hab)) => H1.
by move: (H1 x1); rewrite /setI E2.
Qed.

Section OpSet.

Variables d: finType.
Variables d': eqType.
Variable a: set d.
Variable S:  d -> set d'.
Variable setOp : set d' -> set d' -> set d'.

Definition setnOp := 
  foldr (fun z => setOp (S z)) set0 (filter a (enum d)).

End OpSet.

Section Unions.

Variables d: finType.
Variables d': eqType.
Variable a: set d.
Variable S:  d -> set d'.

(**********************************************************************)
(*                                                                    *)
(*  Definition of the union of indexed sets                           *)
(*                                                                    *)
(**********************************************************************)

Definition setnU := setnOp a S setU.
(*
Definition setnU := 
  foldr (fun z => setU (S z)) set0 (filter a (enum d)).
*)

Lemma setnUP: forall x,
  reflect (exists y, a y && S y x) (setnU x).
move => x; rewrite / setnU / setnOp; apply: (iffP idP) => Hx.
 have: (exists y, ((filter a (enum d) y) && S y x)).
   elim: (enum d) Hx => [| x1 s1 Hx1] //=.
   case: (a x1) => //=.
     case/orP => H1; first 
       by exists x1; rewrite /setU1 eq_refl.
     case: Hx1 => // y; case/andP => Hy1 Hy2.
     by exists y; rewrite /setU1 Hy1 orbT.
 case => y; case/andP => Hy1 Hy2; exists y.
 by rewrite -(filter_enum a) Hy1.
have F1: (exists y, ((filter a (enum d) y) && S y x)).
 case Hx => y; case/andP => Hy1 Hy2; exists y.
 by rewrite filter_enum Hy1.
elim: (enum d) F1 => [| x1 s1 Hx1] //=.
  by case.
case: (a x1) => //; case => y; case/andP => /=; 
  case/orP => Hy1 Hy2; apply/orP => //.
  by left; rewrite (eqP Hy1).
by right; apply: Hx1; exists y; rewrite Hy1.
Qed.

End Unions.

Lemma setnU0: forall (d: finType) d' (S: d -> set d'),
  setnU set0 S =1 set0.
Proof.
by move => d d' S x; rewrite / setnU / setnOp filter_set0.
Qed.

Lemma setnU1: forall (d: finType) d' x (S: d -> set d'),
  setnU (set1 x) S =1 S x.
Proof.
move => d d' x S y; apply/idP/idP => H.
  by case/setnUP: H => y1; case/andP => Hy1 Hy2;
     rewrite (eqP Hy1).
by apply/setnUP; exists x; rewrite eq_refl.
Qed.

Lemma eq_setnU: forall (d: finType) d' a b (S: d -> set d'),
  a =1 b -> setnU a S =1 setnU b S.
Proof.
by move => d d' a b S H x; apply/setnUP/setnUP => [] [y Hy];
   exists y; rewrite ?H // -H.
Qed.

Lemma setnU_setU: forall (d: finType) d' (a b: set d) (S: d -> set d'),
  setnU (setU a b) S =1 setU (setnU a S) (setnU b S).
move => d d' a b S x; apply/setnUP/orP.
  case => y; case/andP; case/orP => H1 H2.
    by left; apply/setnUP; exists y; rewrite H1.
  by right; apply/setnUP; exists y; rewrite H1.
by case; case/setnUP => y; case/andP => Hy1 Hy2;
   exists y; rewrite /setU Hy1 // orbT.
Qed.

Lemma setnU_disjoint: forall (d d': finType) (a: set d) 
                         (S: d -> set d') (A: set d'),
  (forall x, a x -> disjoint A (S x)) ->
  disjoint A (setnU a S).
move => d d' a S A.
elim: {a}(card a) {-2}a (refl_equal (card a)) =>
   [| n Hrec a Hc Hp].
  move => a H1 H2; rewrite /disjoint /set0b.
  apply/eqP; apply: eq_card0 => x.
  rewrite /setI /= (@eq_setnU _ _ _ set0 S).
    by rewrite setnU0 andbF.
  by apply card0_eq.
have F1: ~~set0b a.
  by apply/set0P => H1; rewrite (eq_card0 H1) in Hc.
case/set0Pn: F1 => x Hx.
rewrite /disjoint /set0b; apply/eqP; apply eq_card0 => x1.
rewrite /setI (@eq_setnU _ _ _ (setU (set1 x) (setD1 a x)) S); last 
 by move => x2; rewrite /set1 /setU; 
    case E1: (EqType.eq x x2) => //=;
    first (by rewrite -(eqP E1)); rewrite /setD1 /eqtype.set1 E1.
rewrite setnU_setU /setU setnU1.
apply/andP => [] [H1 H2].
case/orP: H2 => H2.
  move/set0P: (Hp _ Hx) => H3; move: (H3 x1).
  by rewrite /setI H1 H2.
have F1: card (setD1 a x) = n.
  apply (@addn_injl 1%N).
  by rewrite (add1n n) -Hc (cardD1 x a) Hx.
have F2: forall x1, setD1 a x x1 -> disjoint A (S x1).
  move => x2 Hx2; apply: Hp.
  by case/andP: Hx2.
move/set0P: (Hrec _ F1 F2) => H3; move: (H3 x1).
by rewrite /setI H1 H2.
Qed.

Lemma sum_setnU: forall (d d': finType) (a: set d) 
                         (S: d -> set d') (N: d'-> nat),
  disjointn a S ->
  sum (setnU a S) N = 
  sum a (fun z => sum (S z) N).
move => d d' a S N.
elim: {a}(card a) {-2}a (refl_equal (card a)) =>
   [| n Hrec] a Ha Da.
  move: (card0_eq Ha) => Ha1.
  by rewrite (eq_sum N (eq_setnU S Ha1))
             (eq_sum N (setnU0 _)) (eq_sum _ Ha1) !sum0.
have F1: ~~set0b a.
  by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F1 => x Hx.
have F2: a =1 setU (set1 x) (setD1 a x).
  move => x1; rewrite /setU /setD1.
  by case E1: (x == x1) => //=; rewrite -(eqP E1).
have F3: card (setD1 a x) = n.
  apply (@addn_injl 1%N).
  by rewrite (add1n n) -Ha (cardD1 x a) Hx.
have F4: disjoint (set1 x) (setD1 a x).
  apply/set0P => x1; apply/negP; case/andP => H1. 
  by rewrite (eqP H1) setD11.
rewrite (eq_sum _ F2) sum_setU //.
rewrite (eq_sum N (eq_setnU S F2)).
rewrite (eq_sum _ (setnU_setU _ _ _)) sum_setU.
  congr addn; first by rewrite (eq_sum _ (setnU1 _ _)) sum1.
  apply: Hrec => //.
  move => x1 y1 z1 Hx1 Hy1 Hxy.
  apply: (Da x1 y1 z1) => //.
    by case/andP: Hx1.
  by case/andP: Hy1.
apply: setnU_disjoint => x2.
case/andP => Hx1 Hx2.
apply/set0P => x3; rewrite /setI setnU1. 
  case E1: (S x x3) => //.
  case E2: (S x2 x3) => //.
  by case/negP: Hx1; rewrite (Da _ _ x3 Hx Hx2) // E2.
Qed.

Lemma card_disjoint: forall (d: finType) (a b: set d),
  disjoint a b -> card (setU a b) = card a + card b.
Proof.
move => d a b Hab; rewrite -(cardIC b) addnC; congr addn;
   apply eq_card => x1; rewrite /setI /setU /setC;
   case E1: (a x1); case E2: (b x1) => //.
rewrite /disjoint /set0b in Hab.
move: (card0_eq (eqP Hab)) => H1.
by move: (H1 x1); rewrite /setI E1 E2.
Qed.

Lemma card_setnU: forall (d d': finType) (a: set d) 
                         (S: d -> set d'),
  disjointn a S ->
  card (setnU a S) = sum a (fun z => card (S z)) .
move => d d' a S H.
rewrite sum_card sum_setnU //.
by apply: eq_sumf => x H1; rewrite sum_card.
Qed.

Lemma card_setnU_id: forall (d d': finType) (a: set d) 
                         (S: d -> set d') l,
  disjointn a S -> (forall x, a x -> card (S x) = l) ->
  card (setnU a S) = card a * l.
move => d d' a S l Ds Ch.
rewrite card_setnU //; exact: sum_id.
Qed.

Lemma card_dvdn_setnU: forall (d d': finType) (a: set d) 
                         (S: d -> set d') l,
  wdisjointn a S -> (forall x, a x -> dvdn l (card (S x))) ->
  dvdn l (card (setnU a S)).
move => d d' a S l Ds Ch.
elim: {a}(card a) {-2}a (refl_equal (card a)) Ds Ch =>
   [| n Hrec] a Ds Ch In.
  rewrite (eq_card (eq_setnU _ (card0_eq Ds))).
  by rewrite (eq_card (setnU0 _)) card0 dvdn0.
have F1: ~~set0b a.
  by apply/set0P => H1; rewrite (eq_card0 H1) in Ds.
case/set0Pn: F1 => x Hx.
have F1: a =1 setU (set1 x) (setD1 a x).
  move => x1; rewrite /setU /setD1.
  by case E1: (x == x1) => //=; rewrite -(eqP E1).
have F2: card (setD1 a x) = n.
  apply (@addn_injl 1%N).
  by rewrite (add1n n) -Ds (cardD1 x a) Hx.
have F3: disjoint (set1 x) (setD1 a x).
  apply/set0P => x1; apply/negP; case/andP => H1. 
  by rewrite (eqP H1) setD11.
rewrite (eq_card (eq_setnU _ F1)) (eq_card (setnU_setU _ _ _)).
case F4: (disjoint (setnU (set1 x) S) (setnU (setD1 a x) S)).
  rewrite card_disjoint // dvdn_addr.
    apply: Hrec => //; first 
      by move => x1 x2 s1 Hx1 Hx2 Hx12; apply: (Ch x1 x2 s1); 
                case/andP: Hx1; case/andP: Hx2.
    by move => x1 Hx1; apply In; case/andP: Hx1.
  rewrite (eq_card (setnU1 _ _)). 
  exact: In. 
set S1 := (setnU _ _); set S2 := (setnU _ _).
have F5: setU S1 S2 =1 S2.
  move => x1; apply/orP/idP; last by right.
  case => // => H1; case H2: (S2 x1) => //.
  move/set0Pn: F4.
  case => y; case/andP; rewrite setnU1 => H3.
  case/setnUP => x2; case/andP => Hx2 Hx3.
  case/negP: H2; apply/setnUP.
  exists x2; rewrite Hx2 /=.
  rewrite -(Ch x x2 y) //.
    by move: H1; rewrite /S1 setnU1. 
  by case/andP: Hx2.
rewrite (eq_card F5) /S2.
apply: Hrec => //; first 
  by move => x1 x2 s1 Hx1 Hx2 Hx12; apply: (Ch x1 x2 s1); 
             case/andP: Hx1; case/andP: Hx2.
by move => x1 Hx1; apply In; case/andP: Hx1.
Qed.

Section Partition.

Variables d: finType.
Variables d': finType.
Variable a: set d.
Variable S:  d -> set d'.
Variable A: set d'.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being a cover:                                      *)
(*    union S_i = A                                                   *)
(*                                                                    *)
(**********************************************************************)

Definition cover:= (subset (setnU a S) A) && (subset A (setnU a S)).

Lemma coverP:
  reflect ((forall x, a x -> subset (S x) A) /\
           (forall x, A x -> exists i, a i && S i x))
           cover.
Proof.
apply: (iffP idP).
  case/andP; move/subsetP => H1; move/subsetP => H2; split.
    move => x Hx; apply/subsetP => i Hi; apply: H1.
    by apply/setnUP; exists x; rewrite Hx.
  move => i Hi; case/setnUP: (H2 _ Hi) => x Hx.
  by exists x.
case => H1 H2; apply/andP; split; apply/subsetP => i Hi.
  case/setnUP: Hi => x; case/andP => Hx1 Hx2. 
  move/subsetP: (H1 _ Hx1) => H3; exact: H3.
case: (H2 _ Hi) => x Hx.
by apply/setnUP; exists x.
Qed.

Lemma eq_cover: 
  reflect ((setnU a S) =1 A) cover.
Proof.
apply: (iffP idP) => H.
  case/andP: H; move/subsetP => H1; move/subsetP => H2.
  move => x; apply/idP/idP => Hx; first exact: H1.
  exact: H2.
by rewrite /cover (eq_subset H) (eq_subset_r H) !subset_refl.    
Qed.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being a partition:                                  *)
(*    indexed sets that are disjoint and form a cover                 *)
(*                                                                    *)
(**********************************************************************)

Definition partition := disjointn a S /\ cover.

Lemma card_partition: partition ->
  card A = sum a (fun z => card (S z)).
case => H1 H2.
move/eq_cover: H2 => H2.
rewrite -(eq_card H2).
exact: card_setnU.
Qed.

Lemma card_partition_id: forall l, partition ->
  (forall x, a x -> card (S x) = l) ->
  card A = card a * l.
move => l Hp He; rewrite card_partition //.
exact: sum_id.
Qed.

(**********************************************************************)
(*                                                                    *)
(*  Definition of being a weakpartition:                              *)
(*    indexed sets that are weakly disjoint and form a cover          *)
(*                                                                    *)
(**********************************************************************)

Definition wpartition := wdisjointn a S /\ cover.

Lemma partitionW:
  partition -> wpartition.
Proof.
case => H1 H2; split => //; exact: disjointnW.
Qed.

Lemma card_dvdn_partition: forall l, wpartition ->
  (forall x, a x -> dvdn l (card (S x))) ->
  dvdn l (card A).
Proof.
move => l Hp He.
case: Hp => H1 H2.
move/eq_cover: H2 => H2.
rewrite -(eq_card H2).
exact: card_dvdn_setnU.
Qed.

End Partition.

           
(**********************************************************************)
(*                                                                    *)
(*  Preimage of elements of the image form a partition                *)
(*                                                                    *)
(**********************************************************************)

Section fun_partition.

Variable d: finType.
Variable d': finType.
Variable a: set d.
Variable f: d -> d'.

Lemma partition_preimage: 
  partition (image f a) (fun x => setI (preimage f (set1 x)) a) a.
Proof.
split.
  by rewrite /disjointn => u v x H1 H2;case/andP => H3 H4;
     case/andP => H5 H6; rewrite (eqP H3) (eqP H5).
apply/andP;split; apply/subsetP => x; last move => Hax.
  by case/setnUP => y; case/andP => _ ;case /andP.
apply /setnUP;exists (f x).
by rewrite image_f_imp // /setI Hax andbT /preimage /=.
Qed.

End fun_partition.

(**********************************************************************)
(*                                                                    *)
(*  Boolean forall for finType                                        *)
(*                                                                    *)
(**********************************************************************)


Notation "'forallb' x : A , f " :=  
  (set0b (preimage (fun (x : A) => f) (set1 false))) (at level 95, x at level 99).

Theorem forallP: forall (A: finType) (P: A -> bool), 
   reflect (forall (x: A), (P x))
           (forallb x: A, (P x)).
Proof.
move => A P; apply: (iffP idP).
  move/set0P => H1 x; move: (H1 x).
  by move/negPn.
move => H1; apply/set0P => x.
by apply/negPn.
Qed.

Theorem forallPn: forall (A: finType) (P: A -> bool), 
   reflect (exists x: A, ~(P x))
           (~~(forallb x: A, (P x))).
Proof.
move => A P; apply: (iffP idP).
  move/set0Pn => [x].
  by move/negPn => Hx; exists x.
move => [x Hx]; apply/set0Pn.
by exists x; apply/negPn.
Qed.

Notation "'existsb' x : A , f" :=  
  (~~(set0b (preimage (fun (x : A) => f) (set1 true)))) (at level 0, x at level 99).

Theorem existsP: forall (A: finType) (P: A -> bool), 
   reflect (exists x: A, (P x))
           (existsb x: A, (P x)).
Proof.
move => A P; apply: (iffP idP).
  move/set0Pn => [x].
  rewrite /preimage; move/eqP => H1.
  by exists x.
move => [x Hx].
apply/set0Pn.
by exists x; apply/eqP.
Qed.

Theorem existsPn: forall (A: finType) (P: A -> bool), 
   reflect (forall x: A, ~(P x))
           (~~(existsb x: A, (P x))).
Proof.
move => A P; apply: (iffP idP).
  move => H1 x Hx.
  case/set0Pn: H1; exists x.
  by apply/eqP.
move => H; apply/set0Pn.
move => [x Hx]; case: (H x).
move/eqP: Hx; rewrite /preimage.
by move/eqP; move/eqP.
Qed.

(**********************************************************************)
(*                                                                    *)
(*  Boolean injective for finType                                     *)
(*                                                                    *)
(**********************************************************************)


Section Injectiveb.

Variable d d': finType.
Variable f: d -> d'.

Definition injectiveb := 
 forallb x: d, forallb y: d, f x == f y ->b x == y.

Lemma injectiveP: (reflect (injective f) injectiveb).
Proof.
apply: (iffP idP).
  move => H x y Hx.
  move/forallP: H; move /(_ x).
  move/forallP; move /(_ y).
  by rewrite Hx eq_refl; move/eqP.
move => H; apply/forallP => x; apply/forallP => y.
case E1: (f x == f y) => //.
by rewrite (H _ _ (eqP E1)) eq_refl.
Qed.

Lemma injectiveN: ~(injective f) ->
  exists x, exists y, (x != y) && (f x == f y).
Proof.
move/injectiveP; move/forallPn => [x].
move/negP; move/forallPn => [y H].
exists x; exists y.
by move: H; case: (_ == _) => //; case: (_ == _).
Qed.

Variable a: set d.

Definition dinjectiveb := 
 forallb x: d, forallb y: d,
   a x && a y && (f x == f y) ->b x == y.

Lemma dinjectiveP: (reflect (dinjective a f) dinjectiveb).
Proof.
apply: (iffP idP).
  move/forallP => H x y Hx Hy; move/eqP => H1.
  move/forallP: (H x); move /(_ y).
  by rewrite Hx Hy H1; move/eqP.
move => H; apply/forallP => x; apply/forallP => y.
case Ex: (a x) => //.
case Ey: (a y) => //.
case E1: (f x == f y) => //.
by rewrite (H _ _ Ex Ey (eqP E1)) eq_refl.
Qed.

Lemma dinjectivePn: 
  reflect 
   (exists x, exists y, a x && a y && (x != y) && (f x == f y))
   (~~dinjectiveb).
Proof.
apply: (iffP idP).
  move/forallPn => [x].
  move/negP; move/forallPn => [y Hxy].
  exists x; exists y.
  move: Hxy; do 2 case: (a _) => //.
  by do 2 case: (_ == _).
case => x; case => y; (do 3 case/andP) => E1 E2 E3 E4.
apply/negP => H; move/forallP: H; move /(_ x).
move/forallP; move /(_ y) => HH.
case/negP: E3; apply: (implP _ _ HH).
by rewrite E1 E2.
Qed.

End Injectiveb.

Section Eq1b.

Variable d: finType.
Variable a b: set d.
Definition eq1b:= forallb x: d, a x == b x.

Lemma eq1P: reflect (a =1 b) eq1b.
Proof.
apply: (iffP idP).
  by move/forallP => H x; apply/eqP.
by move => H; apply/forallP => x; apply/eqP.
Qed.

Lemma eq1Pn: reflect (exists x, (a x <> b x)) (~~ eq1b).
Proof.
apply: (iffP idP).
  case/forallPn => x Hx; exists x => Hx1.
  by case Hx; rewrite Hx1.
case => x Hx; apply/forallPn; exists x => Hx1.
by case: Hx; apply/eqP.
Qed.
 
End Eq1b.

Notation "a '=1b' b" := (eq1b a b) (at level 70, no associativity).




Unset Implicit Arguments.


