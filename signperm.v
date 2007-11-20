Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp action.
Require Import normal.

Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.

(* We don't use the bool group structure directly here, but we may need it to *)
(* make the parity function is a morphism S_n -> bool, e.g., to define A_n as *)
(* its kernel.                                                                *)
Canonical Structure boolGroup :=
  @FinGroupType _ _ (fun b => b) addb addFb addbb addbA.

(* Porting the eqType / finType structure of eq_pair to pairs *)
(* To be complete we should also port the group structure, to *)
(* get the direct product.                                    *)

Section PermutationComplements.

Variable d : finType.

(* This should really be in group_perm *)

(* This is a crutch: if permutations coerced to fgraphs, this *)
(* wouln't be needed.                                         *)
Lemma p2f : forall f Uf, @Perm d (EqSig _ (fgraph_of_fun f) Uf) =1 f.
Proof. move=> *; exact: g2f. Qed.

Lemma perm1 : forall x, (1 : permType d) x = x.
Proof. by move=> x; rewrite p2f. Qed.

Lemma permM : forall (s1 s2 : permType d) x, (s1 * s2) x = s2 (s1 x).
Proof. by move=> *; rewrite p2f. Qed.

Lemma permK : forall s : permType d, cancel s s^-1.
Proof. by move=> s x; rewrite -permM mulgV perm1. Qed. 

Lemma permKv : forall s : permType d, cancel s^-1 s.
Proof. by move=> s; have:= permK s^-1; rewrite invgK. Qed.

Lemma permJ : forall (s t: permType d) x, (s ^ t) (t x) = t (s x).
Proof. by move=> *; rewrite !permM permK. Qed.

End PermutationComplements.

(* Shorten the name for tranpositions, to improve usability *)

Notation transp := (@transperm _).

Section PermutationParity.

Variable d : finType.

(* Lifting permutations to pairs, with local shorthand. *)

Definition perm_pair (s : permType d) p :=
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
  forall s A p, image (permp s) A p = A (permp s^-1 p).
Proof. by move=> s A p; rewrite -{1}(permpK s^-1 p) invgK (image_f _ (permpI s)). Qed.

Notation Local im_permp := image_perm_pair.

(* Flipping components of a pair *)

Definition flip_pair A p : A * A := let: (x, y) := p in (y, x).
Notation Local flip := (@flip_pair d).

Lemma flip_pairK : involutive flip.
Proof. by case. Qed.
Notation Local flipK := flip_pairK.

Definition flip_pair_inj := inv_inj flipK.
Notation Local flipI := flip_pair_inj.

Lemma image_flip_pair : forall p A, image flip A p = A (flip p).
Proof. by move=> p A; rewrite -{1}(flipK p) (image_f _ flipI). Qed.
Notation Local im_flip := image_flip_pair.

Lemma perm_flip_pair : forall s p, permp s (flip p) = flip (permp s p).
Proof. by move=> s [x y]. Qed.
Notation Local permp_flip := perm_flip_pair.

(* Inversions are defined abstractly in terms of an "ordered_pair" relation. *)
(* The only required properties for that relation are antisymmetry and       *)
(* antirelexivity, which are conveniently expressed in terms of the "flip"   *)
(* operation. The actual definition compares indices, but we don't use the   *)
(* transitivity, except in an alternate proof that transpositions are odd.   *)

Definition ordered_pair p := index (fst p) (enum d) < index (snd p) (enum d).
Notation Local opair := ordered_pair.

Lemma ordered_pair_flip : forall p, opair (flip p) = (flip p != p) && ~~ opair p.
Proof.
case=> x y /=; rewrite /opair ltn_neqAle -leqNgt; congr andb; congr negb.
rewrite {2}/set1 /= /pair_eq /= (eq_sym y) andbb; apply/eqP/eqP=> [|-> //].
by rewrite -{2}(sub_index x (mem_enum y)) => ->; rewrite sub_index // mem_enum.
Qed.
Notation Local opair_flip := ordered_pair_flip.

Definition inversion s p := opair (flip (permp s p)).
Notation Local invn := inversion.

Definition odd_perm s := odd (card (setI opair (inversion s))).
Definition even_perm s := ~~ odd_perm s.
Notation Local oddp := odd_perm.

Lemma odd_permM : forall s t, oddp (s * t) = oddp s (+) oddp t.
Proof.
move=> s t; rewrite /oddp -(cardIC (inversion s)); symmetry.
rewrite -(cardIC (inversion (s * t))) addbC -(card_image (permpI s^-1)) -(cardIC opair).
rewrite !odd_addn addbCA !addbA -addbA addbC -addbA; set n1 := card _; set n2 := card _.
suffices -> : n2 = n1.
  rewrite addbK /setI /setC; congr 2 (odd _ (+) odd _); apply: eq_card=> p /=.
    by rewrite andbC andbCA andbA.
  rewrite im_permp invgK /inversion -permpM !opair_flip -!permp_flip !(inj_eq (permpI _)).
  by case: (_ != p); rewrite ?andbF //= negbK -andbA andbC -!andbA andbCA.
rewrite /n2 -(card_image flipI); apply: eq_card => p /=.
rewrite /setI /setC im_flip im_permp invgK /inversion !permp_flip !flipK -permpM.
by rewrite !opair_flip -permp_flip (inj_eq (@permpI _)) -!andbA; do !bool_congr.
Qed.
Notation Local oddpM := odd_permM.

Lemma odd_perm1 : oddp 1 = false.
Proof. by rewrite -[1]mulg1 oddpM addbb. Qed.
Notation Local oddp1 := odd_perm1.

Lemma odd_permV : forall s, oddp s^-1 = oddp s.
Proof. by move=> s; rewrite -{2}(mulgK s s) !oddpM addbb. Qed.
Notation Local oddpV := odd_permV.

Lemma odd_permJ : forall s t, oddp (s ^ t) = oddp s.
Proof. by move=> *; rewrite /conjg !oddpM oddpV addbC addbA addbb. Qed.
Notation Local oddpJ := odd_permJ.


(* Complements on tranpositions, starting with a shorter prenex alias. *)

CoInductive transp_spec (x y z : d) : d -> Type :=
  | TranspFirst of z = x          : transp_spec x y z y
  | TranspSecond of z = y         : transp_spec x y z x
  | TranspNone of z <> x & z <> y : transp_spec x y z z.

Lemma transpP : forall x y z, transp_spec x y z (transp x y z).
Proof. by move=> x y z; rewrite p2f /transpose; do 2?[case: eqP => /=]; constructor; auto. Qed.

Lemma transpL : forall x y : d, transp x y x = y.
Proof. by move=> x y; case transpP. Qed.

Lemma transpR : forall x y : d, transp x y y = x.
Proof. by move=> x y; case transpP. Qed.

Lemma transpC : forall x y : d, transp x y = transp y x.
Proof. by move=> *; apply: eq_fun_of_perm => ?; do 2![case: transpP => //] => ->. Qed.

Lemma transp1 : forall x : d, transp x x = 1.
Proof. by move=> *; apply: eq_fun_of_perm => ?; rewrite perm1; case: transpP. Qed.

Lemma transpK : forall x y : d, involutive (transp x y).
Proof. by move=> x y z; do 2![case transpP => //] => ->. Qed.

Lemma transpV : forall x y : d, (transp x y)^-1 = transp x y.
Proof.
by move=> x y; apply: eq_fun_of_perm => z; rewrite -{1}(transpK x y z) permK.
Qed.

Lemma transp2 : forall x y : d, transp x y * transp x y = 1.
Proof. by move=> x y; rewrite -{1}transpV mulVg. Qed.

Lemma inj_transp : forall (d' : finType) (f : d -> d') x y z,
  injective f -> f (transp x y z) = transp (f x) (f y) (f z).
Proof. by move=> d' f x y z injf; rewrite !p2f /transpose !(inj_eq injf) !(fun_if f). Qed.

Lemma transpJ : forall x y (s : permType d), (transp x y)^s = transp (s x) (s y).
Proof.
move=> x y s; apply: eq_fun_of_perm => z; rewrite -(permKv s z) permJ.
apply: inj_transp; exact: perm_inj.
Qed.

Lemma odd_transp : forall x y, oddp (transp x y) = (x != y).
Proof.
move=> x y; case Dxy: (x == y); first by rewrite (eqP Dxy) transp1 oddp1.
without loss Oxy: x y Dxy / opair (x, y).
  case Oxy: (opair (x, y)); last rewrite transpC; apply=> //; first by rewrite eq_sym.
  by rewrite (opair_flip (x, y)) Oxy andbT; apply/nandP; right; rewrite Dxy.
pose A z p := let: (x', y') := p : d * d in set2 x' y' z.
pose B z p := opair p && inversion (transp x y) p && A z p.
have:= congr1 odd (cardUI (B x) (B y)); rewrite !odd_addn.
have->: card (B x) = card (B y); last rewrite addbb.
  rewrite -(card_image (permpI (transp x y))) -(card_image flipI).
  apply: eq_card => p; rewrite /= /setI im_flip im_permp transpV.
  rewrite /B /inversion !permp_flip flipK -permpM transp2 permp1 -!andbA; do !bool_congr.
  by case: p => x' y'; rewrite /A /= /set2 !(inv_eq (transpK _ _)) orbC transpL.
move/(fun H => canRL H (addKb _)) => /=.
have->: odd (card (setU (B x) (B y))) = oddp (transp x y); last move->.
  congr odd; apply: eq_card=> p /=; rewrite /setI /setU /B.
  case: (@andP (opair p)) => //=; case; rewrite /inversion opair_flip => Op; case/andP=> _ Otp.
  apply/norP; case; rewrite /A; case: p => [x' y'] /= in Op Otp *.
  do 2![case/norP; do 2!move/eqP=> ?]; case/negP: Otp; do 2![case transpP => //].
rewrite -[true]/(odd 1) -(card1 (x, y)); congr odd.
apply: eq_card => [[x' y']]; rewrite /setI {}/B {}/A /inversion /= /set1 /= /pair_eq /=.
rewrite /set2 !(eq_sym x) !(eq_sym y); case: eqP => [-> | _] /=.
  by rewrite Dxy; case: eqP => [->|_]; [rewrite transpL transpR Oxy | rewrite !andbF].
apply/and3P; case; case/andP=> _; move/eqP=> -> Oxx'; rewrite Dxy orbF; move/eqP=> Dx'.
by rewrite Dx' -(flipK (y, x)) opair_flip /= Oxy andbF in Oxx'.
Qed.

(* An alternate proof, based on reduction by conjugation.
   It's less abstract, since it depends on the way pairs are ordered.
Lemma signature_transp' : forall x y, oddp (transp x y) = (x != y).
Proof.
move=> x y; have x0 := x; pose z i := sub x0 (enum d) i; pose n := size (enum d).
wlog ->: x y / x = z 0.
  pose p := transp x (z 0); rewrite -(inj_eq (@perm_inj _ p)) -(oddpJ _ p) transpJ.
  apply; exact: transpL.
case Dy0: (z 0 == y) {x} => /=.
  rewrite -oddp1; congr oddp; apply: eq_fun_of_perm => x.
  by rewrite (eqP Dy0) perm1; case transpP.
have Ez: forall i, i < n -> index (z i) (enum d) = i.
  move=> i ltid; exact: index_uniq ltid (uniq_enum d).
have Iz: exists2 i, i < n & z i = _ by move=> t; apply/subP; exact: mem_enum.
have eqz: forall i j, i < n -> j < n -> (z i == z j) = (i == j).
  move=> i j; move/Ez=> Di; move/Ez=> Dj.
  by apply/eqP/eqP=> [Dzi | -> //]; rewrite -Di Dzi Dj.
have lt1n: 1 < n; last have lt0n := ltnW lt1n.
  case: (Iz y) => [i ltin Dy]; rewrite -{}Dy in Dy0.
  by apply: leq_trans ltin; case: i Dy0 => //; rewrite set11.
wlog{Dy0} ->: y / y = z 1%nat.
  rewrite -(oddpJ _ (transp y (z 1%nat))) transpJ => Wy.
  case: transpP; by [move/eqP; rewrite ?Dy0 ?eqz | rewrite transpL Wy].
rewrite -[true]/(odd 1) -{2}(card1 (z 0, z 1%nat)) {y}; congr odd.
apply: eq_card=> [[u1 u2]]; case: (Iz u1) (Iz u2) => [i1 i1P <-] [i2 i2P <-] {u1 u2}.
do 2!rewrite /set1 /=; rewrite /setI /inversion /opair /= !Ez //.
rewrite /fun_of_perm !g2f /transpose -!(fun_if z) !eqz //.
case: i2 i1 => [|[|i2]] [|[|i1]] //= in i1P i2P *; rewrite !Ez //= !ltnS.
by apply/andP; case=> lti12; rewrite ltnNge ltnW.
Qed.
*)

(** Definitions of the alternate groups and some Properties **)
Definition sym := Group (group_set_finGroupType (perm_finGroupType d)).

Lemma dom_odd_perm : dom odd_perm = (perm_finGroupType d).
Proof.
apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP=> x //.
move=> _; case Ix : (odd_perm x);  [rewrite dom_nu // | rewrite dom_k //].
  by rewrite Ix.
apply/kerP=> y; move: Ix; rewrite odd_permM.
by case: odd_perm.
Qed.

Lemma group_set_dom_odd_perm : group_set (dom odd_perm).
Proof.
by rewrite dom_odd_perm; apply/andP; split => //; apply/subsetP=> u.
Qed.

Definition sign_morph: morphism (perm_finGroupType d) boolGroup.
exists odd_perm.
  exact: group_set_dom_odd_perm.
move => *; exact: odd_permM.
Defined.

Definition alt :=  Group (group_set_ker sign_morph).

Lemma altP: forall x, reflect (even_perm x) (alt x).
Proof.
move => x; apply: (iffP idP); rewrite /even_perm => H1.
  by move: (mker H1) => /= ->.
apply/kerP => /= y.
by move: H1; rewrite odd_permM; case: odd_perm.
Qed.

Lemma alt_subset: subset alt sym.
Proof.
by apply/subsetP => x; rewrite !s2f.
Qed.

Lemma alt_normal: alt <| sym.
Proof.
rewrite /isetA /= -dom_odd_perm.
exact: (normal_ker sign_morph).
Qed.

Lemma alt_index: 1 < card d -> indexg alt sym = 2.
Proof.
move => H.
have F1: ker_(sym) oddp = alt.
  apply/isetP => z; apply/idP/idP; rewrite /isetI /= s2f.
    by case/andP.
  by move => -> /=; rewrite s2f.
rewrite <- card_quotient; last by exact: alt_normal.
rewrite <- F1.
have F: isog (sym/ ker_(sym) oddp) (odd_perm @: sym).
  have F2: subset sym (dom oddp).
    by rewrite dom_odd_perm; apply/subsetP.
  exact: (@first_isom _ _ sign_morph _ F2).
case: F => g; case/andP => H1; move/injmP => /= H2.
rewrite /= in H1.
rewrite -(card_diimage H2) (eqP H1).
have <-: card boolGroup = 2.
  by rewrite eq_cardA // => x; rewrite s2f.
apply eq_card => z; apply/idP/idP.
  by rewrite s2f.
case: z => _ /=; last first.
  apply/iimageP; exists (1:perm_finGroupType d) => //.
  by rewrite odd_perm1.
case: (pickP d) => [x1 Hx1 | HH]; move: H; last first.
  by rewrite (eq_card HH) card0.
rewrite (cardD1 x1) Hx1.
case: (pickP (setD1 d x1)) => [x2 Hx2 | HH1]; last first.
  by rewrite (eq_card HH1) card0.
case/andP: Hx2 => Hx2 Hy2 _.
apply/iimageP; exists (transperm x1 x2) => //=.
by rewrite odd_transp.
Qed.

Let n := card (setA d).

Let setAd: card d = card (setA d).
by rewrite eq_cardA // => x; rewrite s2f.
Qed.

Lemma card_alt: 1 < card d -> (2* (card alt))%N= fact n.
move => Hcard; move: (LaGrange alt_subset).
rewrite mulnC alt_index // /n => ->.
rewrite - (card_perm (setA d)).
apply:eq_card=> /=.
by move =>  z; rewrite s2f; apply sym_equal;apply/subsetP. 
Qed.


Let gt1: tuple.tuple_finType d n.
exists (enum d).
by rewrite card_ordinal.
Defined.

Definition dsym1: dtuple d n.
exists gt1.
rewrite /gt1 /distinctb /=.
exact: uniq_enum.
Defined.

Let d2p_aux:
 forall (t: seq d),
 size t = card (setA I_(n)) ->  size t = card (setA d).
Proof.
by move => t; rewrite card_ordinal.
Qed.

Definition d2p: dtuple d n -> (permType d).
move => [[t Hs] Ht].
apply Perm.
by exists (Fgraph (d2p_aux Hs)).
Defined.

Lemma d2p_sym: forall t, sym (d2p t).
Proof.
by move => [[t Ht] Dt]; rewrite s2f.
Qed.

Lemma eq_maps_s : forall (d1 d2: eqType) (f1 f2 : d1 -> d2) (l: seq d1), 
  (forall x, l x ->  f1 x = f2 x) -> maps f1 l = maps f2 l.
move => d1 d2 f1 f2; elim => [|a l Hrec] H //=.
rewrite (H a) // ?Hrec //= /setU1 ?eq_refl //.
by move => x H1; rewrite H //= /setU1 H1 orbT.
Qed.

Lemma eq_maps_same : forall (d1: eqType) (l1 l2: seq d1)
                             (f: d1 -> d1),
  size l1 = size l2 -> uniq l2 ->
  maps (fun z => sub (f z) l1 (index z l2)) l2 = l1.
move => d1; elim => [| b l1 Hrec] [|c l2] //=.
move => f Hs; case/andP => H1 H2; rewrite eq_refl /=.
congr Adds.
rewrite -{2}(Hrec l2 f) //.
  refine (eq_maps_s _).
  move => e He.
  case Ec: (e == c) => //.
  by case/negP: H1; rewrite -(eqP Ec).
by injection Hs.
Qed.

Lemma d2p_sym1: forall t,
   naction (perm_act d) n dsym1 (d2p t) = t.
move => [[t Ht] Dt]; apply/val_eqP => /=.
rewrite /set1 /= /to  /fun_of_perm /=.
rewrite /fun_of_fgraph; unlock; rewrite /=.
apply/eqP; apply: eq_maps_same.
  by rewrite Ht card_ordinal.
exact: uniq_enum.
Qed.

Lemma sym_trans: ntransitive (perm_act d) sym (setA d) n.
Proof.
split; last by exact: max_card.
move => x Hx y; apply/iimageP/idP => [[z Hz Hz1] | H1].
  by exact: dliftA.
exists ((d2p x)^-1 * (d2p y)).
  by rewrite s2f.
rewrite act_morph.
rewrite -{1}(d2p_sym1 x) -!act_morph; gsimpl.
by rewrite (d2p_sym1 y).
Qed.


Lemma alt_trans: ntransitive (perm_act d) alt (setA d) (n - 2).
Proof.
case (leqP n 2).
  rewrite -eqn_sub0; move/eqP => ->; exact: ntransitive0.
move => Hn.
have Hn1: 1 < n by apply: leq_trans Hn.
have Hn2: n = n - 2 + 1 + 1.
  by rewrite -addnA addnC leq_add_sub.
have Hn3: 0 < n - 2 + 1 + 1 
  by rewrite -Hn2; apply: leq_trans Hn1.
have Hn4: 0 < n - 2 + 1.
  by rewrite addnC ltnS leq_eqVlt ltn_0sub Hn orbT.
split; last first.
  by rewrite -/n leq_subr.
move => x Hx y; apply/iimageP/idP => [[z Hz ->] | H1].
  by exact: dliftA.
have F: card(setC (dtuple_get x)) == 2.
  by rewrite -(eqn_addr (n - 2)) leq_add_sub //
          -{2}(dtuple_get_card x) addnC cardC.
case: (pickP (setC (dtuple_get x))) => 
        [a1 Ha1 | HH]; last first.
  by move: F; rewrite (eq_card HH) card0.
case: (pickP (setD1 (setC (dtuple_get x)) a1)) => 
        [a2 {F}Ha2 | HH]; last first.
  by move: F; rewrite (cardD1 a1) (eq_card HH) Ha1 card0.
have F: card(setC (dtuple_get y)) == 2.
  by rewrite -(eqn_addr (n - 2)) leq_add_sub //
          -{2}(dtuple_get_card y) addnC cardC.
case: (pickP (setC (dtuple_get y))) => 
        [b1 Hb1 | HH]; last first.
  by move: F; rewrite (eq_card HH) card0.
case: (pickP (setD1 (setC (dtuple_get y)) b1)) => 
        [b2 {F}Hb2 | HH]; last first.
  by move: F; rewrite (cardD1 b1) (eq_card HH) Hb1 card0.
set x1 := dtuple_add Ha1.
have Fx1: ~~ dtuple_in a2 x1.
  rewrite /x1 /dtuple_in.
  case: (x) (Ha1) (Ha2); case => /= v _ _ _.
  by case/andP => HH1 HH2; apply/norP; split.
set x2 := dtuple_add Fx1.
set y1 := dtuple_add Hb1.
have Fy1: ~~ dtuple_in b2 y1.
  rewrite /y1 /dtuple_in /distinctb.
  case: (y) (Hb1) (Hb2); case => /= v _ _ _.
  by case/andP => HH1 HH2; apply/norP; split.
set y2 := dtuple_add Fy1.
move: sym_trans.
rewrite {1}Hn2; case => FF _.
move: (dliftA y2); rewrite -(@FF _ (dliftA x2)).
case/iimageP => g Hg Hg1.
case Pm: (odd_perm g); last first.
  exists g => [/= |].
    by apply/kerP => h; rewrite odd_permM Pm.
  have ->: x = (dtuple_tl (dtuple_tl x2))
    by rewrite !dtuple_tl_add.
  by rewrite -!naction_tl -Hg1 !dtuple_tl_add.
set (g1:= transperm b1 b2).
exists (g * g1) => [/= |].
  apply/kerP => h; rewrite !odd_permM Pm odd_transp.
  by case/andP: (Hb2) => ->.
have ->: x = (dtuple_tl (dtuple_tl x2))  
  by rewrite !dtuple_tl_add.
rewrite act_morph -!naction_tl -Hg1.
have Fy3: ~~ dtuple_in b2 y.
  rewrite /dtuple_in /distinctb.
  case: (y) (Hb1) (Hb2); case => /= v _ _ _.
  by case/andP.
set y3 := dtuple_add Fy3.
have Fy4: ~~ dtuple_in b1 y3.
  rewrite /y3 /dtuple_in /distinctb /=.
  case: (y) (Fy3) (Hb1) (Hb2) => [[v]] /= _ _ _ HH.
  case/andP => HH1 HH2; apply/norP; split => //.
  by rewrite eq_sym.
set y4 := dtuple_add Fy4.
suff ->: naction (perm_act d) (n -2 + 1 + 1) y2 g1 = y4.
  by rewrite !dtuple_tl_add.
apply: (dtuple_hd_tl (x:= a1)).
  rewrite dtuple_hd_add naction_hd /= /to /g1 //
          dtuple_hd_add.
  by case: (transpP b1 b2 b2).
rewrite dtuple_tl_add naction_tl dtuple_tl_add.
apply: (dtuple_hd_tl (x:= a1)).
  rewrite dtuple_hd_add naction_hd /= /to /g1 //
          dtuple_hd_add.
  by case: (transpP b1 b2 b1).
rewrite dtuple_tl_add naction_tl dtuple_tl_add.
case: (y) (Hb1) (Fy3); case => /=.
rewrite /dtuple_in /distinctb /setC /= => z Hz Hz0 Hz1 Hz2.
apply/val_eqP => /=; rewrite /set1 /=; apply/eqP.
elim: (z) Hz1 Hz2 =>  [|a z1 Hrec] //=.
case/norP => Hz3 Hz4; case/norP => Hz5 Hz6.
congr Adds; last by exact: Hrec.
rewrite /to /g1 /=.
by case: (transpP b1 b2 a) Hz3 Hz5 => // -> //;
   rewrite eq_refl.
Qed.

End PermutationParity.

Coercion odd_perm : permType >-> bool.
