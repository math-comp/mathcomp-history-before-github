(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*   A small theory of data sets of finite cardinal, based on sequences.     *)
(* A finite data set is a data set plus a duplicate-free sequence of all its *)
(* elements. This is equivalent to requiring only a list, and we do give a   *)
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

Lemma mem_enum : enum d =1 d.
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

Lemma cardA : card d = size (enum d). Proof. exact: count_setA. Qed.

Lemma eq_card0 : forall a, a =1 set0 -> card a = 0.
Proof. by have:= eq_card_trans card0. Qed.

Lemma eq_cardA : forall a, a =1 d -> card a = size (enum d).
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

Lemma cardC : forall a, card a + card (setC a) = card d.
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

Lemma cardC1 : forall x, card (setC1 x) = pred (card d).
Proof. by move=> x; rewrite -(cardC (set1 x)) card1. Qed.

Lemma cardD1 : forall x a, card a = a x + card (setD1 a x).
Proof.
move=> x a; rewrite addnC; apply: (addn_injr (etrans (cardC a) _)).
rewrite -addnA (negb_intro (a x)) -[negb (a x)]/(setC a x) -cardU1.
symmetry; apply: etrans (congr1 (addn _) _) (cardC _).
by apply: eq_card => y; rewrite /setC /setU1 /setD1 negb_andb negb_elim.
Qed.

Lemma max_card : forall a, card a <= card d.
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
Proof. by move=> a Ha x; apply/negP => [Hx]; rewrite (cardD1 x) Hx in Ha. Qed.

Lemma set0P : forall a, reflect (a =1 set0) (set0b a).
Proof. move=> a; apply: (iffP eqP); [apply: card0_eq | apply: eq_card0]. Qed.

Lemma set0Pn : forall a : set d, reflect (exists x, a x) (~~ set0b a).
Proof.
move=> a; case: (set0P a) => [Ha|Hna]; constructor.
  by move=> [x Hx]; case/negP: (Ha x).
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

Lemma subset_setA : forall a, subset a d.
Proof. by move=> a; apply/subsetP. Qed.

Lemma subsetA : forall a, subset d a -> forall x, a x.
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
case/negP: (ltnn (card a)); rewrite {2}Ecab (cardD1 x b) Hbx /setD1.
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

Section FunImage.

Variables (d : finType) (d' : eqType) (f : d -> d').

Definition codom : set d' := fun x' => ~~ set0b (preimage f (set1 x')).

Remark Hiinv : forall x', codom x' -> {x : d | x' == f x}.
Proof.
move=> x' Hx'; pose a := x' == f _.
case: (pickP a) => [x Dx | Hnx']; first by exists x.
by rewrite /codom /preimage -/a (introT set0P Hnx') in Hx'.
Qed.

Definition iinv x' (Hx' : codom x') := let (x, _) := Hiinv Hx' in x.

Lemma codom_f : forall x, codom (f x).
Proof. move=> x; apply/set0Pn; exists x; apply: set11. Qed.

Lemma f_iinv : forall x' (Hx' : codom x'), f (iinv Hx') = x'.
Proof.
by move=> x' Hx'; rewrite /iinv; case: (Hiinv Hx') => [x]; case/eqP.
Qed.

Hypothesis Hf : injective f.

Lemma iinv_f : forall x (Hfx : codom (f x)), iinv Hfx = x.
Proof. move=> x Hfx; apply Hf; apply f_iinv. Qed.

Lemma preimage_iinv : forall a' x' (Hx' : codom x'),
  preimage f a' (iinv Hx') = a' x'.
Proof. by move=> *; rewrite /preimage f_iinv. Qed.

Section Image.

Variable a : set d.

Definition image : set d' := fun x' => ~~ disjoint (preimage f (set1 x')) a.

(* This first lemma does not depend on Hf : (injective f). *)
Lemma image_codom : forall x', image x' -> codom x'.
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

Lemma image_iinv : forall x' (Hx' : codom x'), image x' = a (iinv Hx').
Proof. by move=> x' Hx'; rewrite -image_f f_iinv. Qed.

Lemma pre_image : preimage f image =1 a.
Proof. by move=> x; rewrite /preimage image_f. Qed.

End Image.

Lemma image_pre : forall a', image (preimage f a') =1 setI a' codom.
Proof.
move=> a' x'; rewrite /setI andbC; case Hx': (codom x') => /=.
  by rewrite -(f_iinv Hx') image_f /preimage f_iinv.
apply/idPn => Hax'; case/idP: Hx'; exact (image_codom Hax').
Qed.

Fixpoint preimage_seq (s : seq d') : seq d :=
  if s is Adds x s' then
    (if pick (preimage f (set1 x)) is Some y then Adds y else id) (preimage_seq s')
  else seq0.

Lemma maps_preimage : forall s : seq d',
  sub_set s codom -> maps f (preimage_seq s) = s.
Proof.
elim=> [|x s Hrec] //=; case: pickP => [y Dy|Hs'] Hs.
  rewrite /= (eqP Dy) Hrec // => z Hz; apply Hs; exact: setU1r.
by case/set0P: (Hs x (setU11 _ _)).
Qed.

End FunImage.

Prenex Implicits codom iinv image.

Section Ordinal.

Variable n : nat.

Definition ord_enum := subfilter (fun m => m < n) (iota 0 n).

Lemma ord_enumP : forall u, count (set1 u) ord_enum = 1.
Proof.
move=> [p Hp]; rewrite count_set1_uniq /ord_enum.
  by rewrite mem_subfilter /preimage /setI /= mem_iota /= andbC andbb Hp.
apply: uniq_subfilter; exact: uniq_iota.
Qed.

Definition ordinal := FinType ord_enumP.

Lemma ordinal_ltn : forall x : ordinal, val x < n.
Proof. by case. Qed.

Lemma card_ordinal : card ordinal = n.
Proof.
rewrite cardA -(size_iota 0 n) /= /ord_enum size_subfilter.
by apply/eqP; rewrite -all_count; apply/allP=> p; rewrite mem_iota.
Qed.

Definition make_ord : forall m, m < n -> ordinal := EqSig (fun m => m < n).

End Ordinal.

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

Lemma card_sub : card sub_finType = card a.
Proof. by rewrite cardA /= /sub_enum size_subfilter. Qed.

Lemma eq_card_sub : forall b, b =1 sub_finType -> card b = card a.
Proof. by have:= eq_card_trans card_sub. Qed.

End SubFinType.

Section ProdFinType.

Variable d1 d2 : finType.

Definition prod_enum :=
  foldr (fun x1 => cat (maps (EqPair x1) (enum d2))) seq0 (enum d1).

Lemma prod_enumP : forall u, count (set1 u) prod_enum = 1.
Proof.
move=> [x1 x2]; rewrite -[1]/(d1 x1 : nat) -mem_enum /prod_enum.
elim: (enum d1) (uniq_enum d1) => [|y1 s1 Hrec] //=; move/andP=> [Hy1 Hs1].
rewrite count_cat {Hrec Hs1}(Hrec Hs1) count_maps /setU1 /comp.
case Hx1: (y1 == x1) => /=.
  rewrite (eqP Hx1) in Hy1; rewrite (negbET Hy1) (eqP Hx1) addn0 -(card1 x2).
  by apply: eq_count => y2; rewrite {1}/set1 /= set11.
rewrite addnC -{2}(addn0 (s1 x1)) -(card0 d2); congr addn.
by apply: eq_count => y; rewrite eq_sym /set1 /= Hx1.
Qed.

Canonical Structure prod_finType := FinType prod_enumP.

Lemma card_prod : forall a1 a2, card (eq_prod a1 a2) = card a1 * card a2.
Proof.
rewrite /card /= /prod_enum => a1 a2; elim: (enum d1) => //= x1 s1 IHs.
rewrite count_cat {}IHs count_maps /comp /eq_prod /=.
by case: (a1 x1); rewrite // count_set0.
Qed.

Lemma eq_card_prod : forall b, b =1 prod_finType -> card b = card d1 * card d2.
Proof. move=> b; rewrite -card_prod; exact: eq_card. Qed.

End ProdFinType.

Section SumFinType.

Variables (index : finType) (dom_at : index -> finType).

Definition finsum_dom_at i : eqType := dom_at i.

Fixpoint sum_enum (si : seq index) : seq (sum_eqType finsum_dom_at) :=
  if si is Adds i si' then
    cat (maps (@EqTagged _ finsum_dom_at i) (enum (dom_at i))) (sum_enum si')
  else seq0.

Lemma sum_enumP : forall u, count (set1 u) (sum_enum (enum index)) = 1.
Proof.
move=> [i x]; rewrite -[1]/(index i : nat) -mem_enum.
elim: (enum index) (uniq_enum index) => [|j s Hrec] //=; case/andP=> [Hj Hs].
rewrite count_cat addnC /= {Hrec Hs}[count _ _](Hrec Hs) addnC.
rewrite count_filter filter_maps size_maps /= /setU1 -count_filter.
case Hi: (j == i); rewrite /= /comp.
  rewrite (eqP Hi) in Hj; rewrite (negbET Hj) (eqP Hi) /= addn0 -(card1 x).
  apply: eq_count => y; exact: sum_eq_tagged.
rewrite addnC -{2}(addn0 (s i)) -(card0 (dom_at j)); congr addn.
by apply: eq_count => y; apply/nandP; left; rewrite /= eq_sym Hi.
Qed.

Canonical Structure sum_finType := FinType sum_enumP.

Lemma card_sum : forall a : eq_family finsum_dom_at,
  card (eq_sum a) = foldr (fun i m => card (a i) + m) 0 (enum index).
Proof.
move=> a; rewrite {1}/card /=; elim: (enum index) => //= [i s <-].
by rewrite count_cat count_maps.
Qed.

Lemma eq_card_sum : forall b, b =1 sum_finType ->
  card b = foldr (fun i m => card (dom_at i) + m) 0 (enum index).
Proof. move=> b; move/eq_card->; exact: card_sum (fun i => @setA (dom_at i)). Qed.

End SumFinType.

Section BijectionCard.

Lemma can_card_leq :  forall (d d' : finType) (f : d -> d') (g : d' -> d),
  cancel f g -> card d <= card d'.
Proof.
move=> d d' f g Hfg; rewrite (cardA d') -(size_maps g).
apply: (leq_trans (subset_leq_card _) (card_size _)).
by apply/subsetP => x _; apply/mapsP; exists (f x); rewrite ?mem_enum.
Qed.

Lemma bij_eq_card_setA : forall d d' : finType,
  (exists f : d -> d', bijective f) -> card d = card d'.
Proof.
move=> d d' [f [g Hfg Hgf]]; apply: eqP.
by rewrite eqn_leq (can_card_leq Hfg) (can_card_leq Hgf).
Qed.

Lemma eq_card_setA : forall d d' : finType, d = d' :> Type -> card d = card d'.
Proof.
move=> d [[d' eqd' eqd'P] ed' Hed'] Hdd'; simpl in Hdd'.
case: d' / Hdd' in eqd' eqd'P ed' Hed' *.
by apply bij_eq_card_setA; do 2 exists (@id d).
Qed.

Lemma bij_eq_card : forall (d d' : finType) (a : set d) (a' : set d'),
 (exists f : sub_finType a -> sub_finType a', bijective f) -> card a = card a'.
Proof. by move=> d d' a a'; move/bij_eq_card_setA; rewrite !card_sub. Qed.

Lemma assoc_finType_default : forall d1 d2 : finType,
  card d1 = card d2 -> d1 -> d2.
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
  card d1 = card d2 -> {f : d1 -> d2 &  {g : d2 -> d1 | cancel f g &  cancel g f}}.
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

Lemma card_codom : card (codom f) = card d.
Proof.
apply: etrans (card_image d); apply: eq_card => x'.
apply/idPn/idP; last exact: image_codom.
by move=> Hx; rewrite -(f_iinv Hx) image_f.
Qed.

Lemma card_preimage : forall a', card (preimage f a') = card (setI (codom f) a').
Proof.
move=> a'; apply: etrans (esym (card_image _)) (eq_card _) => x'.
by rewrite (image_pre Hf) /setI andbC.
Qed.

End CardFunImage.

Unset Implicit Arguments.

