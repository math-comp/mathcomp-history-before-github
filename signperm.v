(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype paths.
Require Import tuple finfun finset.
Require Import connect div groups group_perm zp action.
Require Import normal.

Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

(* We don't use the bool group structure directly here, but we may need it *)
(* to make the parity function is a morphism S_n -> bool, e.g., to define  *)
(* A_n as its kernel.                                                      *)

Canonical Structure boolPreGroup :=
  [baseFinGroupType of bool by addbA, addFb, frefl id & addbC].
Canonical Structure boolGroup := FinGroupType addbb. 

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
by rewrite val_eqE (inj_eq (@enum_rank_inj T)) {2}/eqd /= (eq_sym y) andbb.
Qed.
Notation Local opair_flip := ordered_pair_flip.

Definition inversion s := [pred p | opair (flip (permp s p))].
Notation Local invn := inversion.

Definition odd_perm (s : perm T) := odd #|predI opair (inversion s)|.
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
  rewrite !inE /= !inE /= im_permp inE /= inE /= invgK /= /inversion.
  rewrite -permpM !opair_flip -!permp_flip !(inj_eq (permpI _)).
  by case: (_ != p); rewrite ?andbF //= negbK (andbC (opair p) _) andbA.
rewrite /n2 -(card_image flipI); apply: eq_card => p /=.
rewrite im_flip !inE /= im_permp !inE /= invgK /invn !inE /=.
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
apply: eq_card => [[x' y']]; rewrite inE /= !inE {A B}/= {5}/eqd /=.
rewrite !(eq_sym x) !(eq_sym y) andbA andbC; case: (x' =P x) => [-> | _] /=.
  by rewrite Dxy; case: eqP => //= ->; rewrite tpermL tpermR Oxy.
case: (y' =P x) => /= [->|]; last by rewrite !andbF.
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
Definition sym := setT_group (perm_for_finGroupType T).

Lemma dom_odd_perm : dom odd_perm = setT.
Proof.
apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP=> x //.
move=> _; case Ix : (odd_perm x);  [rewrite dom_nu // | rewrite dom_k //].
  by rewrite Ix.
apply/kerP=> y; move: Ix; rewrite odd_permM.
by case: odd_perm.
Qed.

Lemma group_set_dom_odd_perm : group_set (dom odd_perm).
Proof. rewrite dom_odd_perm; exact: groupP. Qed.

Canonical Structure sign_morph :=
   Morphism group_set_dom_odd_perm (in2W odd_permM).

Definition alt := Group (group_set_ker sign_morph).

Lemma altP : forall p, reflect (even_perm p) (p \in alt).
Proof.
move=> p; rewrite (sameP (kerMP _) negPf); first exact: idP.
by rewrite dom_odd_perm inE.
Qed.

Lemma alt_subset : alt \subset sym.
Proof. by apply/subsetP => x _; rewrite inE. Qed.

Lemma alt_normal : alt <| sym.
Proof. by rewrite -[sym : set _]dom_odd_perm; exact: normal_ker. Qed.

Lemma alt_norm : sym \subset 'N(alt).
Proof. by case/andP: alt_normal. Qed.

Let n := #|T|.

Lemma alt_index : 1 < n -> indexg alt sym = 2.
Proof.
move=> lt1n; rewrite -card_quotient ?alt_norm //= -ker_r_dom dom_odd_perm.
have [g]: isog (sym / ker_(sym) sign_morph) (odd_perm @: sym).
  by apply: first_isom; rewrite dom_odd_perm subset_refl.
case/andP=> im_quo; move/injmP; move/card_dimset <-; move/eqP: im_quo => ->{g}.
rewrite eq_cardT // => b; apply/imsetP; case: b => /=; last first.
  by exists (1 : perm T); [rewrite inE | rewrite odd_perm1].
case: (pickP T) lt1n => [x1 _ | d0]; last by rewrite /n eq_card0.
rewrite /n (cardD1 x1) ltnS lt0n; case/existsP=> x2 /=.
by rewrite eq_sym andbT -odd_tperm; exists (tperm x1 x2); rewrite ?inE.
Qed.

Lemma card_sym : #|sym| = fact n.
Proof.
rewrite -[n]cardsE -card_perm; apply: eq_card => p.
by apply/idP/subsetP=> [? ?|]; rewrite !inE.
Qed.

Lemma card_alt : 1 < n -> (2 * #|alt|)%N = fact n.
Proof.
by move/alt_index <-; rewrite mulnC (LaGrange alt_subset) card_sym.
Qed.

Definition sym1 : tuple n T := [tuple of enum T].

Lemma d2p_inject_aux : forall s : tuple n T,
  dtuple_on T s -> injective (fun x => tsub s (enum_rank x)).
Proof.
move=> s; case/dtuple_onP=> s_inj _ x y; move/s_inj; exact: enum_rank_inj.
Qed.

Definition d2p s ds := perm_of (@d2p_inject_aux s ds).

Lemma d2p_sym: forall t (dt : dtuple_on T t), d2p dt \in sym.
Proof. by move=> *; rewrite inE. Qed.

Lemma d2p_sym1 : forall t (dt : dtuple_on T t),
  n_act (perm_action T) sym1 (d2p dt) = t.
Proof.
move=> t dt; apply: eq_from_tsub => i; rewrite tsub_maps.
rewrite [perm_action _ _ _]permE; congr tsub.
by rewrite (tsub_sub (enum_default i)) enum_valK.
Qed.

Lemma sym_trans: ntransitive (perm_action T) sym T n.
Proof.
split; last by exact: max_card.
move=> x Hx y; apply/imsetP/idP => [[z Hz ->] | Hy].
  exact: n_act_dtuple.
exists ((d2p Hx)^-1 * (d2p Hy)); first by rewrite inE.
by rewrite actM -{1}(d2p_sym1 Hx) /= actK (d2p_sym1 Hy).
Qed.

Lemma alt_trans: ntransitive (perm_action T) alt T (n - 2).
Proof.
case: (leqP n 2) => [|lt2n].
  by rewrite -eqn_sub0; move/eqP => ->; exact: ntransitive0.
have lt1n: 1 < n by exact: ltnW.
split; [move=> /= x Hx y | by rewrite -/n leq_subr].
apply/imsetP/idP => [[z Hz ->] | Hy]; first exact: n_act_dtuple.
have: #|[predC x]| == 2.
  rewrite -(eqn_addr (n - 2)) subnK //.
  suff Hf: #|x| = n - 2 by rewrite addnC -{1}Hf cardC.
  by rewrite (card_uniqP _) ?size_tuple //; case/andP: Hx.
case: (pickP [predC x]) => /= [a1 Ha1 | HH]; last by rewrite eq_card0.
case: (pickP (predD1 [predC x] a1)) => /= [a2 Ha2 _ | HH]; last first.
  by rewrite (cardD1 a1) inE /= Ha1 eq_card0.
have: #|[predC y]| == 2.
  rewrite -(eqn_addr (n - 2)) subnK //.
  suff Hf: #|y| = n - 2 by rewrite addnC -{1}Hf cardC.
  by rewrite (card_uniqP _) ?size_tuple //; case/andP: Hy.
case: (pickP [predC y]) => /= [b1 Hb1 | HH]; last by rewrite eq_card0.
case: (pickP (predD1 [predC y] b1)) => /= [b2 Hb2 _ | HH]; last first.
  by rewrite (cardD1 b1) inE /= Hb1 eq_card0.
pose x1 := [tuple of a2 :: a1 :: x]; pose y1 := [tuple of b2 :: b1 :: y].
have:= sym_trans; rewrite -{1}(subnK lt1n) add2n; case => FF _.
have Dnx1: dtuple_on T x1 by rewrite !dtuple_on_add Ha1 negb_or Ha2.
have: dtuple_on T y1 by rewrite !dtuple_on_add Hb1 negb_or Hb2.
rewrite -[dtuple_on T y1](@FF _ Dnx1); case/imsetP => g Hg Hg1.
case Pm: (odd_perm g); last first.
  exists g; first by apply/kerP => h; rewrite /= odd_permM Pm.
  by apply: val_inj; case/(congr1 val): Hg1.
pose g1:= tperm b1 b2; exists (g * g1) => [/= |].
  apply/kerP => h; rewrite !odd_permM Pm odd_tperm eq_sym.
  by case/andP: Hb2 => ->.
rewrite actM; apply: val_inj; case/(congr1 val): Hg1 => /= ga1 ga2 <-.
rewrite dmaps_id // => c yc; rewrite /perm_to /g1.
by case/andP: Hb2 => _; case: tpermP Hb1 => // <-; rewrite yc.
Qed.

Lemma perm_action_faithful: faithful (perm_action T) alt T.
Proof.
apply/faithfulP=> /= p np1; apply/eqP; apply/perm_act1P.
by move=> y; case: (np1 y).
Qed.

End PermutationParity.

Coercion odd_perm : perm >-> bool.
