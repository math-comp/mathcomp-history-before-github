(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import tuple finset groups perm action prim_act.
Require Import morphisms normal.

(* Require Import paths finfun connect div zp. *)

Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

(* We don't use the bool group structure directly here, but we may need it *)
(* to make the parity function is a morphism S_n -> bool, e.g., to define  *)
(* A_n as its kernel.                                                      *)

Definition bool_groupMixin := FinGroup.Mixin addbA addFb addbb.
Canonical Structure bool_baseGroup :=
  Eval hnf in BaseFinGroupType bool_groupMixin.
Canonical Structure boolGroup := Eval hnf in FinGroupType addbb. 

Section PermutationParity.

Variable T : finType.

(* Lifting permutations to pairs, with local shorthand. *)

Definition perm_pair (s : {perm T}) p :=
  let: (x, y) := p in (s x, s y).
Notation Local permp := perm_pair.

Lemma perm_pair1 : forall p, permp 1 p = p. 
Proof. by move=> [x y] /=; rewrite !perm1. Qed.
Notation Local permp1 := perm_pair1.

Lemma perm_pairM : forall s t p, permp (s * t) p = permp t (permp s p).
Proof. by move=> s t [x y] /=; rewrite !permM. Qed.
Notation Local permpM := perm_pairM.

Lemma perm_pairK : forall s, cancel (permp s) (permp s^-1).
Proof. by move=> s p; rewrite -permpM mulgV permp1. Qed.
Notation Local permpK := perm_pairK.

Definition perm_pair_inj s := can_inj (permpK s).
Notation Local permpI := (@perm_pair_inj).
Hint Resolve perm_pair_inj.

Lemma image_perm_pair : 
  forall s A, image (permp s) A =i preim (permp s^-1) A.
Proof.
move=> s A p.
by rewrite -!topredE /= -{1}(permpK s^-1 p) invgK (image_f _ (permpI s)).
Qed.

Notation Local im_permp := image_perm_pair.

(* Flipping components of a pair *)

Definition flip_pair A p : A * A := let: (x, y) := p in (y, x).
Notation Local flip := (@flip_pair T).

Lemma flip_pairK : involutive flip.
Proof. by case. Qed.
Notation Local flipK := flip_pairK.

Definition flip_pair_inj := inv_inj flipK.
Notation Local flipI := flip_pair_inj.

Lemma image_flip_pair : forall A, image flip A =i preim flip A.
Proof.
by move=> A p; rewrite -!topredE /= -{1}(flipK p) (image_f _ flipI).
Qed.
Notation Local im_flip := image_flip_pair.

Lemma perm_flip_pair : forall s p, permp s (flip p) = flip (permp s p).
Proof. by move=> s [x y]. Qed.
Notation Local permp_flip := perm_flip_pair.

(* Inversions are defined abstractly in terms of an "ordered_pair" relation. *)
(* The only required properties for that relation are antisymmetry and       *)
(* antirelexivity, which are conveniently expressed in terms of the "flip"   *)
(* operation. The actual definition compares indices, but we don't use the   *)
(* transitivity, except in an alternate proof that transpositions are odd.   *)

Definition ordered_pair : pred (T * T) :=
   fun p => enum_rank p.1 < enum_rank p.2.
Notation Local opair := ordered_pair.

Lemma ordered_pair_flip : forall p,
  opair (flip p) = (flip p != p) && ~~ opair p.
Proof.
case=> x y; rewrite /opair ltn_neqAle -leqNgt; congr (~~ _ && _).
by rewrite val_eqE (inj_eq (@enum_rank_inj T)) {2}/eq_op /= (eq_sym y) andbb.
Qed.
Notation Local opair_flip := ordered_pair_flip.

Definition inversion s := [pred p | opair (flip (permp s p))].
Notation Local invn := inversion.

Definition odd_perm (s : perm_type T) := odd #|predI opair (inversion s)|.
Notation Local oddp := (odd_perm : pred {perm T}).
Definition even_perm s := ~~ oddp s.

Lemma odd_permM : {morph oddp : s t / s * t >-> s (+) t}.
Proof.
move=> s t; rewrite /oddp -(cardID (inversion s)); symmetry.
rewrite -(cardID (inversion (s * t))) addbC.
rewrite -(card_image (permpI s^-1)) -(cardID opair).
rewrite !odd_add addbCA !addbA -addbA addbC -addbA.
set n1 := card _; set n2 := card _.
suffices -> : n2 = n1.
  rewrite addbK /=; congr 2 (odd _ (+) odd _); apply: eq_card=> p /=.
    by rewrite !inE /= andbC andbCA andbA.
  rewrite !inE im_permp !inE invgK /= /inversion.
  rewrite -permpM !opair_flip -!permp_flip !(inj_eq (permpI _)).
  by case: (_ != p); rewrite ?andbF //= negbK (andbC (opair p) _) andbA.
rewrite /n2 -(card_image flipI); apply: eq_card => p /=.
rewrite im_flip !inE im_permp !inE invgK /invn.
rewrite !permp_flip !flipK -permpM !opair_flip -permp_flip.
by rewrite (inj_eq (@permpI _)) -!andbA; do !bool_congr.
Qed.
Notation Local oddpM := odd_permM.

Lemma odd_perm1 : oddp 1 = false.
Proof. by rewrite -[1]mulg1 oddpM addbb. Qed.
Notation Local oddp1 := odd_perm1.

Lemma odd_permV : forall s, oddp s^-1 = oddp s.
Proof. by move=> s; rewrite -{2}(mulgK s s) !oddpM addbb. Qed.
Notation Local oddpV := odd_permV.

Lemma odd_permJ : forall s t, oddp (s ^ t) = oddp s.
Proof. by move=> *; rewrite /conjg !oddpM oddpV addbCA addbb addbF. Qed.
Notation Local oddpJ := odd_permJ.


(* Complements on tranpositions, starting with a shorter prenex alias. *)

CoInductive tperm_spec (x y z : T) : T -> Type :=
  | TpermFirst of z = x          : tperm_spec x y z y
  | TpermSecond of z = y         : tperm_spec x y z x
  | TpermNone of z <> x & z <> y : tperm_spec x y z z.

Lemma tpermP : forall x y z, tperm_spec x y z (tperm x y z).
Proof.
move=> x y z; rewrite permE /transpose.
by do 2?[case: eqP => /=]; constructor; auto.
Qed.

Lemma tpermL : forall x y : T, tperm x y x = y.
Proof. by move=> x y; case tpermP. Qed.

Lemma tpermR : forall x y : T, tperm x y y = x.
Proof. by move=> x y; case tpermP. Qed.

Lemma tpermD : forall x y z : T,  x != z -> y != z -> tperm x y z = z.
Proof. by move => x y z; case tpermP => // ->; rewrite eqxx. Qed.

Lemma tpermC : forall x y : T, tperm x y = tperm y x.
Proof. by move=> *; apply/permP => ?; do 2![case: tpermP => //] => ->. Qed.

Lemma tperm1 : forall x : T, tperm x x = 1.
Proof. by move=> *; apply/permP => ?; rewrite perm1; case: tpermP. Qed.

Lemma tpermK : forall x y : T, involutive (tperm x y).
Proof. by move=> x y z; do 2![case tpermP => //] => ->. Qed.

Lemma tpermV : forall x y : T, (tperm x y)^-1 = tperm x y.
Proof.
by move=> x y; apply/permP => z; rewrite -{1}(tpermK x y z) permK.
Qed.

Lemma tperm2 : forall x y : T, tperm x y * tperm x y = 1.
Proof. by move=> x y; rewrite -{1}tpermV mulVg. Qed.

Lemma inj_tperm : forall (T' : finType) (f : T -> T') x y z,
  injective f -> f (tperm x y z) = tperm (f x) (f y) (f z).
Proof.
move=> T' f x y z injf.
by rewrite !permE /transpose !(inj_eq injf) !(fun_if f).
Qed.

Lemma tpermJ : forall x y (s : {perm T}), (tperm x y) ^ s = tperm (s x) (s y).
Proof.
move=> x y s; apply/permP => z; rewrite -(permKV s z) permJ.
apply: inj_tperm; exact: perm_inj.
Qed.

Lemma odd_tperm : forall x y, oddp (tperm x y) = (x != y).
Proof.
move=> x y; case Dxy: (x == y); first by rewrite (eqP Dxy) tperm1 oddp1.
without loss Oxy: x y Dxy / opair (x, y).
  case Oxy: (opair (x, y)); last rewrite tpermC; apply=> //; first by rewrite eq_sym.
  by rewrite (opair_flip (x, y)) Oxy andbT; apply/nandP; right; rewrite Dxy.
pose A z : pred (T * T) := fun p => let: (x', y') := p in pred2 x' y' z.
pose B z := [pred p | opair p && inversion (tperm x y) p && A z p].
have:= congr1 odd (cardUI (B x) (B y)); rewrite !odd_add.
have->: #|B x| = #|B y|; last rewrite addbb.
  rewrite -(card_image (permpI (tperm x y))) -(card_image flipI).
  apply: eq_card => p; rewrite /= !inE /= im_flip inE /= im_permp inE /=.
  rewrite tpermV inE /= !permp_flip flipK -permpM tperm2 permp1.
  rewrite -!andbA; do !bool_congr.
  by case: p => x' y'; rewrite /= -!(inv_eq (tpermK _ _)) tpermL orbC.
move/(canRL (addKb _)) => /=.
have->: odd #|predU (B x) (B y)| = oddp (tperm x y); last move->.
  congr odd; apply: eq_card=> p /=; rewrite !inE /=.
  case: (@andP (opair p)) => //=; case; rewrite opair_flip => Op.
  case/andP=> _; case: p => /= x' y' in Op *.
  by do 2![case: tpermP=> [->|->|_ _]; rewrite ?(eqxx, orbT) //]; case/negP.
rewrite -[true]/(odd 1) -(card1 (x, y)); congr odd.
apply: eq_card => /= [[x' y']]; rewrite inE /= !inE {A B}/= {5}/eq_op /=.
rewrite !(eq_sym x) !(eq_sym y) andbA andbC.
case: (x' == x) / (x' =P x) => [-> | _] /=.
  rewrite Dxy; case: (y' == y) / (y' =P y) => //= ->.
  by rewrite tpermL tpermR Oxy.
case: (y' == x) / (y' =P x) => /= [->|]; last by rewrite !andbF.
rewrite Dxy orbF -andbA; case: eqP => // ->; rewrite tpermL tpermR !andbb /=.
by rewrite -(flipK (y, x)) opair_flip Oxy andbF.
Qed.

  (* An alternate proof, based on reduction by conjugation.
   It's less abstract, since it depends on the way pairs are ordered. *)
(* NOT UPDATED
Lemma odd_tperm' : forall x y, oddp (tperm x y) = (x != y).
Proof.
move=> x y; have x0 := x; pose z i := sub x0 (enum T) i; pose n := size (enum T).
wlog ->: x y / x = z 0.
  pose p := tperm x (z 0); rewrite -(inj_eq (@perm_inj _ p)) -(oddpJ _ p) tpermJ.
  apply; exact: tpermL.
case Dy0: (z 0 == y) {x} => /=.
  rewrite -oddp1; congr oddp; apply/permP => x.
  by rewrite (eqP Dy0) perm1; case tpermP.
have Ez: forall i, i < n -> index (z i) (enum T) = i.
  move=> i ltid; exact: index_uniq ltid (uniq_enum T).
have Iz: exists2 i, i < n & z i = _ by move=> t; apply/subP; exact: mem_enum.
have eqz: forall i j, i < n -> j < n -> (z i == z j) = (i == j).
  move=> i j; move/Ez=> Di; move/Ez=> Dj.
  by apply/eqP/eqP=> [Dzi | -> //]; rewrite -Di Dzi Dj.
have lt1n: 1 < n; last have lt0n := ltnW lt1n.
  case: (Iz y) => [i ltin Dy]; rewrite -{}Dy in Dy0.
  by apply: leq_trans ltin; case: i Dy0 => //; rewrite eqxx.
wlog{Dy0} ->: y / y = z 1%nat.
  rewrite -(oddpJ _ (tperm y (z 1%nat))) tpermJ => Wy.
  case: tpermP; by [move/eqP; rewrite ?Dy0 ?eqz | rewrite tpermL Wy].
rewrite -[true]/(odd 1) -{2}(card1 (z 0, z 1%nat)) {y}; congr odd.
apply: eq_card=> [[u1 u2]]; case: (Iz u1) (Iz u2) => [i1 i1P <-] [i2 i2P <-] {u1 u2}.
do 2!rewrite /pred1 /=; rewrite /= /inversion /opair /= !Ez //.
rewrite /fun_of_perm !ffunE /transpose -!(fun_if z) !eqz //.
case: i2 i1 => [|[|i2]] [|[|i1]] //= in i1P i2P *; rewrite !Ez //= !ltnS.
by apply/andP; case=> lti12; rewrite ltnNge ltnW.
Qed.
*)

(** Definitions of the alternate groups and some Properties **)
Definition Sym of phant T : {set {perm T}} := setT.

Canonical Structure Sym_group phT := Eval hnf in [group of Sym phT].

Notation Local "'Sym_T" := (Sym (Phant T)) (at level 0).

Canonical Structure sign_morph := @Morphism _ _ 'Sym_T _ (in2W odd_permM).

Definition Alt of phant T := 'ker odd_perm.

Canonical Structure Alt_group phT := Eval hnf in [group of Alt phT].

Notation Local "'Alt_T" := (Alt (Phant T)) (at level 0).

Lemma Alt_even : forall p, (p \in 'Alt_T) = even_perm p.
Proof. by move=> p; rewrite !inE /even_perm /=; case: odd_perm. Qed.

Lemma Alt_subset : 'Alt_T \subset 'Sym_T.
Proof. exact: subsetT. Qed.

Lemma Alt_normal : 'Alt_T <| 'Sym_T.
Proof. exact: ker_normal. Qed.

Lemma Alt_norm : 'Sym_T \subset 'N('Alt_T).
Proof. by case/andP: Alt_normal. Qed.

Let n := #|T|.

Lemma Alt_index : 1 < n -> #|'Sym_T : 'Alt_T| = 2.
Proof.
move=> lt1n; rewrite -card_quotient ?Alt_norm //=.
have : ('Sym_T / 'Alt_T) \isog (odd_perm @* 'Sym_T) by apply: first_isog.
case/isogP=> g; move/injmP; move/card_in_imset <-.
rewrite /morphim setIid=> ->; rewrite -card_bool; apply: eq_card => b.
apply/imsetP; case: b => /=; last first.
 by exists (1 : {perm T}); [rewrite setIid inE | rewrite odd_perm1].
case: (pickP T) lt1n => [x1 _ | d0]; last by rewrite /n eq_card0.
rewrite /n (cardD1 x1) ltnS lt0n; case/existsP=> x2 /=.
by rewrite eq_sym andbT -odd_tperm; exists (tperm x1 x2); rewrite ?inE.
Qed.

Lemma card_Sym : #|'Sym_T| = fact n.
Proof.
rewrite -[n]cardsE -card_perm; apply: eq_card => p.
by apply/idP/subsetP=> [? ?|]; rewrite !inE.
Qed.

Lemma card_Alt : 1 < n -> (2 * #|'Alt_T|)%N = fact n.
Proof.
by move/Alt_index <-; rewrite mulnC (LaGrange Alt_subset) card_Sym.
Qed.

Lemma Sym_trans : [transitive * n ('Sym_T | 'P) on setT].
Proof.
apply/imsetP; pose t1 := [tuple of enum T].
have dt1: t1 \in n.-dtuple(setT) by rewrite inE uniq_enum; apply/subsetP.
exists t1 => //; apply/setP=> t; apply/idP/imsetP=> [|[a _ ->{t}]]; last first.
  by apply: n_act_dtuple => //; apply/astabsP=> x; rewrite !inE.
case/dtuple_onP=> injt _; have injf := inj_comp injt (@enum_rank_inj _).
exists (perm injf); first by rewrite inE.
apply: eq_from_tsub => i; rewrite tsub_maps /= [aperm _ _]permE; congr tsub.
by rewrite (tsub_sub (enum_default i)) enum_valK.
Qed.

Lemma Alt_trans : [transitive * n.-2 ('Alt_T | 'P) on setT].
Proof.
case n_m2: n Sym_trans => [|[|m]] /= tr_m2; try exact: ntransitive0.
have tr_m := ntransitive_weak (leqW (leqnSn m)) tr_m2.
case/imsetP: tr_m2; case/tupleP=> x; case/tupleP=> y t.
rewrite !dtuple_on_add 3!inE negb_or /= -!andbA; case/and4P=> nxy ntx nty dt _.
apply/imsetP; exists t => //; apply/setP=> u.
apply/idP/imsetP=> [|[a _ ->{u}]]; last first.
  by apply: n_act_dtuple => //; apply/astabsP=> z; rewrite !inE.
case/(atransP2 tr_m dt)=> /= a _ ->{u}.
case odd_a: (odd_perm a); last by exists a => //; rewrite !inE /= odd_a.
exists (tperm x y * a); first by rewrite !inE /= odd_permM odd_tperm nxy odd_a.
apply: val_inj; apply: eq_in_maps => z tz; rewrite actM /= /aperm; congr (a _).
by case: tpermP ntx nty => // <-; rewrite tz.
Qed.

Lemma aperm_faithful : forall A : {group {perm T}},
  [faithful (A | 'P) on setT].
Proof.
move=> A; apply/faithfulP=> /= p _ np1; apply/eqP; apply/perm_act1P=> y.
by rewrite np1 ?inE.
Qed.

End PermutationParity.

Notation "''Sym_' T" := (Sym (Phant T))
  (at level 8, T at level 2, format "''Sym_' T") : group_scope.
Notation "''Sym_' T" := (Sym_group (Phant T)) : subgroup_scope.

Notation "''Alt_' T" := (Alt (Phant T))
  (at level 8, T at level 2, format "''Alt_' T") : group_scope.
Notation "''Alt_' T" := (Alt_group (Phant T)) : subgroup_scope.

Coercion odd_perm : perm_type >-> bool.
