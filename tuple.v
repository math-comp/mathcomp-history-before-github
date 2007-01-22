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

Section FinGraph.
Variable d1 d2 : finType.

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

Definition infgraph (s : seq d2) : option fgraphType :=
  if size s =P (card (setA d1)) is Reflect_true Hs then Some (Fgraph Hs) else None.

CoInductive infgraph_spec (s : seq d2) : option fgraphType -> Type :=
  | Some_tup u : size s = (card (setA d1)) -> fval u = s -> infgraph_spec s (Some u)
  | None_tup: ~~ (size s == (card (setA d1))) -> infgraph_spec s None.

Lemma infgraphP : forall s, infgraph_spec s (infgraph s).
Proof. by rewrite /infgraph => s; case: eqP; [left | right; exact/eqP]. Qed.

Definition infgraphseq : seq (seq_eqType d2) -> seq fgraph_eqType:=
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
  maps fval finfgraph_enum = mkpermr d2 (card (setA d1)).
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

Definition fgraph_of_fun (f : d1 -> d2) : fgraphType := 
  Fgraph (size_maps f _).

 (* if the domain is not empty the default is the first elem of the graph *)
Lemma fgraph_default : d1 -> fgraphType -> d2.
Proof. by move=> x [[|//]]; rewrite /card; case: enum (mem_enum x). Qed.

Definition fun_of_fgraph g x := 
  sub (fgraph_default x g) (fval g) (locked index x (enum d1)).

Coercion fun_of_fgraph : fgraphType >-> Funclass.

Lemma can_fun_of_fgraph : cancel fun_of_fgraph fgraph_of_fun.
Proof.
rewrite /fun_of_fgraph => g.
case: {-1}g => [s Hs]; apply fval_inj => /=.  
case De: (enum _) => [|x0 e]; first by case: s Hs; rewrite /card De. 
rewrite -De; have y0 := fgraph_default x0 g.
apply: (@eq_from_sub _ y0); rewrite size_maps // => i Hi; unlock.
by rewrite (sub_maps x0) // index_uniq ?uniq_enum ?(set_sub_default y0) ?Hs.
Qed.

Lemma can_fgraph_of_fun : forall f, fgraph_of_fun f =1 f.
Proof.
rewrite /fun_of_fgraph /= => f x; unlock.
by rewrite (sub_maps x) ?sub_index // ?index_mem mem_enum.
Qed.

End FinGraph.

Lemma fgraph_size : forall (T1 T2:finType) (a b:fgraph_eqType T1 T2),
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

Lemma can_uniq:
 forall d : finType, forall d1 : eqType, forall f f1, cancel f1 f ->
 forall u : d1, count (set1 u) (undup (maps f (enum d))) = 1.
Proof.
move => d d1 f f1 Hf1 u.
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
move => f; rewrite /s2s /iset_of_fun; unlock => /=; exact: can_fgraph_of_fun.
Qed.

Definition s2f := can_iset_of_fun.

End SetType.

Notation "{ x , P }" := (iset_of_fun (fun x => P)) (at level 0, x at level 99).
Notation "{ x : T , P }" := (iset_of_fun (fun x : T => P)) (at level 0, x at level 99).

Lemma iset_eq : forall G:finType, forall A B:setType G, A =1 B -> A = B.
Proof.
move => G [t2] [t1]; have Hsize:= fgraph_size t1 t2; have Hg := fproof t2.
rewrite /s2s /fun_of_fgraph /eqfun /=; unlock => H.
apply: sval_inj; apply fval_inj => /=. 
apply: (@eq_from_sub _ true) => // i Hi.
cut G; last first.
  case: G t2 Hg i Hi {H Hsize t1}=> G; case => // Hs t2 Hg i Hi.
  by rewrite /card /= in Hg; rewrite Hg in Hi.
move => e; have {H}:= H (sub e (enum G) i) => H.
rewrite index_uniq in H; [idtac|by rewrite Hg in Hi|exact: uniq_enum].
rewrite (@set_sub_default _ (fval t2) true _ i Hi) in H.
rewrite -Hsize in Hi.
by rewrite (@set_sub_default _ (fval t1) true _ i Hi) in H.
Qed.

Section setTypeOps.

Variable G : finType.

Definition isub_set (A B:setType G) : Prop := forall x : G, A x -> B x.
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

Lemma iset11 : forall x, iset1 x x. 
Proof. move=> x; rewrite s2f; exact: eq_refl. Qed.

Lemma isetU11 : forall x a, isetU1 x a x.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma isetU1r : forall x a, isub_set a (isetU1 x a).
Proof. by move=> x a y Hy; rewrite s2f Hy orbT. Qed.

Lemma isetU1P : forall x (a : setType G) y, reflect (x = y \/ a y) (isetU1 x a y).
Proof.
by move=>*;rewrite s2f;apply:(iffP orP);case;auto;left;[apply:eqP|apply/eqP].
Qed.

Lemma isetC11 : forall x, isetC1 x x = false.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma isetD11 : forall x a, isetD1 a x x = false.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma iset21 : forall x1 x2, iset2 x1 x2 x1.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma iset22 : forall x1 x2, iset2 x1 x2 x2.
Proof. by move=> *; rewrite s2f eq_refl orbT. Qed.

Lemma iset31 : forall x1 x2 x3, iset3 x1 x2 x3 x1.
Proof. by move=> *; rewrite s2f eq_refl. Qed.

Lemma iset32 : forall x1 x2 x3, iset3 x1 x2 x3 x2.
Proof. by move=> *; rewrite s2f eq_refl !orbT . Qed.

Lemma iset33 : forall x1 x2 x3, iset3 x1 x2 x3 x3.
Proof. by move=> *; rewrite s2f eq_refl !orbT. Qed.

Lemma iset_distrIUr : forall b1 b2 b3 : setType G, 
  isetI b1 (isetU b2 b3) = isetU (isetI b1 b2) (isetI b1 b3).
Proof. move => a b c; apply: iset_eq => x; rewrite !s2f; exact: demorgan1. Qed.

Lemma iset_distrIUl : forall b1 b2 b3:setType G,
  isetI (isetU b1 b2) b3 = isetU (isetI b1 b3) (isetI b2 b3).
Proof. move => a b c; apply: iset_eq => x; rewrite !s2f; exact: demorgan2. Qed.

Lemma iset_distrUIr : forall b1 b2 b3:setType G, 
  isetU b1 (isetI b2 b3) = isetI (isetU b1 b2) (isetU b1 b3).
Proof. move => a b c; apply: iset_eq => x; rewrite !s2f; exact: demorgan3. Qed.

Lemma iset_distrUIl : forall b1 b2 b3:setType G, 
  isetU (isetI b1 b2) b3 = isetI (isetU b1 b3) (isetU b2 b3).
Proof. move => a b c; apply: iset_eq => x; rewrite !s2f; exact: demorgan4. Qed.

Lemma iset_nandP : forall b1 b2:setType G,
  isetU (isetC b1) (isetC b2) = isetC (isetI b1 b2).
Proof. 
by move => a b; apply: iset_eq => x; rewrite !s2f; apply/idP/idP;
  [move => H; apply/nandP; apply/orP|move/nandP => H; apply/orP].
Qed.

Lemma iset_norP : forall b1 b2:setType G,
  isetI (isetC b1) (isetC b2) = isetC (isetU b1 b2).
Proof. 
by move => a b; apply: iset_eq => x; rewrite !s2f; apply/idP/idP;
  [move => H; apply/norP; apply/andP|move/norP => H; apply/andP].
Qed.

Lemma icard1 : forall x, card (iset1 x) = 1.
Proof.
move => x; rewrite /card /iset1 -(@eq_count _ (set1 x)); 
  [exact: FinType.enumP | by move => y; rewrite s2f].
Qed.

Lemma icardUI : forall a b, card (isetU a b) + card (isetI a b) = card a + card b.
Proof. move=> a b. 
rewrite -(@eq_card _ (setU a b)); last by move=>y;rewrite s2f.
rewrite -(@eq_card _ (setI a b) (isetI a b)); last by move=>y;rewrite s2f.
exact: count_setUI. 
Qed.

Lemma icard0 : card iset0 = 0.
Proof.
case: (pickP iset0); first by move => x; rewrite s2f.
move => H; rewrite (eq_card H).
exact: card0.
Qed.

Lemma icardIC : forall b a, card (isetI a b) + card (isetI a (isetC b)) = card a.
Proof.
move=> b a; rewrite -(add0n (card a)) -icardUI addnC -icard0.
by congr (_ + _); apply: eq_card => x; rewrite !s2f;
   case (a x); case (b x).
Qed.

Lemma icardC : forall a:setType G, card a + card (isetC a) = card (setA G).
Proof. move=> a. 
rewrite (cardA G) -(count_setC a) -(@eq_card _ (setC a) (isetC a)) //.
by move=>y; rewrite s2f.
Qed.

(*
Lemma icardU1 : forall x a, card (isetU1 x a) = negb (a x) + card a.
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
Lemma card_uniqP : forall s : seq d, reflect (card s = size s) (uniq s).
Proof.
move=> s; elim: s => [|x s Hrec]; first by left; exact card0.
rewrite /= cardU1 /addn; case (s x); simpl.
  by right; move=> H; move: (card_size s); rewrite H ltnn.
by apply: (iffP Hrec) => [<-| [<-]].
Qed.


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

*)
End setTypeOps.

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
    apply/negPf=> Hx1'; case/negP: Hx1; rewrite eq_sym /fun_of_fgraph; unlock.
    have Hi := He1 x1; rewrite (set_sub_default y0) ?fproof //.
    by move: {Hg}(Hg _ Hi); 
       rewrite (sub_maps x1) // sub_index /e1 ?mem_enum ?Hx1'.
  case/set0Pn: Hx2=> x1; case/andP; move/eqP=> -> {x2} Hx1.
  have Hi := He1 x1; rewrite /fun_of_fgraph (set_sub_default y0) ?fproof //; unlock.
    by move: {Hg}(Hg _ Hi); rewrite (sub_maps x1) // sub_index /e1 ?mem_enum ?Hx1.
  by rewrite cardA.
cut d1; last by move: Hi; rewrite /card; case: (enum d1); auto.
move => x0.
rewrite (sub_maps x0) //; set x1 := sub _ _ i.
have <-: g x1 = sub y0 (fval g) i.
  by rewrite /fun_of_fgraph (set_sub_default y0) /x1; unlock;
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

Canonical Structure tule_eqType := EqType (@fgraph_eqP domain d).
Canonical Structure tule_finType := FinType (@finfgraph_enumP domain d).

End Tuple.
  
Unset Implicit Arguments.
