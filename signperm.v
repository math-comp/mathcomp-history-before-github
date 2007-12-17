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
move/(canRL (addKb _)) => /=.
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
exists odd_perm; first exact: group_set_dom_odd_perm.
move => *; exact: odd_permM.
Defined.

Definition alt :=  Group (group_set_ker sign_morph).

Lemma altP: forall x, reflect (even_perm x) (alt x).
Proof.
move=> x; apply: (iffP idP); rewrite /even_perm => H1; first by move: (mker H1) => /= ->.
by apply/kerP => /= y; move: H1; rewrite odd_permM; case: odd_perm.
Qed.

Lemma alt_subset: subset alt sym.
Proof.
by apply/subsetP => x; rewrite !s2f.
Qed.

Lemma alt_normal: alt <| sym.
Proof.
by rewrite /isetA /= -dom_odd_perm; exact: (normal_ker sign_morph).
Qed.

Lemma alt_index: 1 < card (setA d) -> indexg alt sym = 2.
Proof.
move=> H.
have F1: ker_(sym) oddp = alt.
  apply/isetP => z; apply/idP/idP; rewrite /isetI /= s2f; first by case/andP.
  by move => -> /=; rewrite s2f.
rewrite -card_quotient ?alt_normal // -F1.
have F: isog (sym/ ker_(sym) oddp) (odd_perm @: sym).
  have F2: subset sym (dom oddp) by rewrite dom_odd_perm; apply/subsetP.
  exact: (@first_isom _ _ sign_morph _ F2).
case: F => g; case/andP => H1; move/injmP => /= H2.
rewrite /= in H1.
rewrite -(card_diimage H2) (eqP H1).
have <-: card boolGroup = 2 by rewrite eq_cardA // => x; rewrite s2f.
apply eq_card => z; apply/idP/idP; first by rewrite s2f.
case: z => _; last first.
  apply/iimageP; exists (1:perm_finGroupType d) => //.
  by rewrite odd_perm1.
case: (pickP (setA d)) => [x1 Hx1 | HH]; move: H; last first.
  by rewrite (eq_card HH) card0.
rewrite (cardD1 x1) Hx1.
case: (pickP (setD1 (setA d) x1)) => [x2 Hx2 | HH1]; last by rewrite (eq_card HH1) card0.
case/andP: Hx2 => Hx2 Hy2 _; apply/iimageP; exists (transperm x1 x2) => //.
by rewrite odd_transp.
Qed.

Let n := card (setA d).

Lemma card_sym: card sym = fact (card (setA d)).
Proof.
by rewrite - (card_perm (setA d)); apply:eq_card =>  z; rewrite s2f; apply sym_equal;apply/subsetP. 
Qed.

Lemma card_alt0: card (setA d) <= 1 -> card alt = 1%N.
move=> Hcard; have cardS: card sym = 1%N.
  by rewrite card_sym; move: Hcard; case: card => // n1; case: n1.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by rewrite -cardS subset_leq_card // alt_subset.
by rewrite (cardD1 1) group1.
Qed.

Lemma card_alt: 1 < card (setA d) -> card alt = divn (fact n) 2.
Proof.
move=> Hcard; suff ->: (fact n = 2 * card alt)%N by rewrite divn_mulr.
by rewrite -card_sym -alt_index 1?mulnC ?LaGrange ?alt_subset.
Qed.

Let gt1: tuple.tuple_finType d n.
by exists (enum d); rewrite card_ordinal.
Defined.

Definition dsym1: dtuple d n.
by exists gt1; rewrite /gt1 /distinctb; exact: uniq_enum.
Defined.

Let d2p_aux:
 forall (t: seq d),
 size t = card (setA I_(n)) ->  size t = card (setA d).
Proof.
by move=> t; rewrite card_ordinal.
Qed.

Definition d2p: dtuple d n -> (permType d).
by move=> [[t Hs] Ht]; apply Perm; exists (Fgraph (d2p_aux Hs)).
Defined.

Lemma d2p_sym: forall t, sym (d2p t).
Proof.
by move=> [[t Ht] Dt]; rewrite s2f.
Qed.

Lemma eq_maps_s : forall (d1 d2: eqType) (f1 f2 : d1 -> d2) (l: seq d1), 
  (forall x, l x ->  f1 x = f2 x) -> maps f1 l = maps f2 l.
Proof.
move=> d1 d2 f1 f2; elim => [|a l Hrec] H //=.
rewrite (H a) // ?Hrec //= /setU1 ?eq_refl //.
by move=> x H1; rewrite H //= /setU1 H1 orbT.
Qed.

Lemma eq_maps_same : forall (d1: eqType) (l1 l2: seq d1)
                             (f: d1 -> d1),
  size l1 = size l2 -> uniq l2 ->
  maps (fun z => sub (f z) l1 (index z l2)) l2 = l1.
Proof.
move=> d1; elim => [| b l1 Hrec] [|c l2] //.
move=> f Hs; case/andP => Hc Hf; rewrite /= eq_refl.
congr Adds; rewrite -{2}(Hrec l2 f) //; last by case: Hs.
apply: eq_maps_s => e He; case Ec: (e == c) => //.
by case/negP: Hc; rewrite -(eqP Ec).
Qed.

Lemma d2p_sym1: forall t,
   naction (perm_act d) n dsym1 (d2p t) = t.
Proof.
move=> [[t Ht] Dt]; apply/val_eqP.
rewrite /set1 /= /to  /fun_of_perm /fun_of_fgraph; unlock.
apply/eqP; apply: eq_maps_same; last by exact: uniq_enum.
by rewrite Ht card_ordinal.
Qed.

Lemma sym_trans: ntransitive (perm_act d) sym (setA d) n.
Proof.
split; last by exact: max_card.
move=> x Hx y; apply/iimageP/idP => [[z Hz Hz1] | H1].
  by exact: dliftA.
exists ((d2p x)^-1 * (d2p y)); first by rewrite s2f.
rewrite act_morph -{1}(d2p_sym1 x) -!act_morph; gsimpl.
by rewrite (d2p_sym1 y).
Qed.

Lemma alt_trans: ntransitive (perm_act d) alt (setA d) (n - 2).
Proof.
case (leqP n 2); first by rewrite -eqn_sub0; move/eqP => ->; exact: ntransitive0.
move => Hn.
have Hn1: 1 < n by apply: leq_trans Hn.
have Hn2: n = n - 2 + 1 + 1. by rewrite -addnA addnC leq_add_sub.
have Hn3: 0 < n - 2 + 1 + 1 by rewrite -Hn2; apply: leq_trans Hn1.
have Hn4: 0 < n - 2 + 1 by rewrite addnC ltnS leq_eqVlt ltn_0sub Hn orbT.
split; last by rewrite -/n leq_subr.
move => x Hx y; apply/iimageP/idP => [[z Hz ->] | H1]; first by exact: dliftA.
have F: card(setC (dtuple_get x)) == 2.
  by rewrite -(eqn_addr (n - 2)) leq_add_sub //
          -{2}(dtuple_get_card x) addnC cardC.
case: (pickP (setC (dtuple_get x))) => 
        [a1 Ha1 | HH]; last by move: F; rewrite (eq_card HH) card0.
case: (pickP (setD1 (setC (dtuple_get x)) a1)) => 
        [a2 {F}Ha2 | HH]; last by move: F; rewrite (cardD1 a1) (eq_card HH) Ha1 card0.
have F: card(setC (dtuple_get y)) == 2.
  by rewrite -(eqn_addr (n - 2)) leq_add_sub //
          -{2}(dtuple_get_card y) addnC cardC.
case: (pickP (setC (dtuple_get y))) => 
        [b1 Hb1 | HH]; last by move: F; rewrite (eq_card HH) card0.
case: (pickP (setD1 (setC (dtuple_get y)) b1)) => 
        [b2 {F}Hb2 | HH]; last by move: F; rewrite (cardD1 b1) (eq_card HH) Hb1 card0.
pose x1 := dtuple_add Ha1; have Fx1: ~~ dtuple_in a2 x1.
  rewrite /x1 /dtuple_in; case: (x) (Ha1) (Ha2); case => /= v _ _ _.
  by case/andP => HH1 HH2; apply/norP; split.
pose y1 := dtuple_add Hb1; have Fy1: ~~ dtuple_in b2 y1.
  rewrite /y1 /dtuple_in /distinctb.
  case: (y) (Hb1) (Hb2); case => /= v _ _ _.
  by case/andP => HH1 HH2; apply/norP; split.
pose x2 := dtuple_add Fx1; pose y2 := dtuple_add Fy1.
move: sym_trans; rewrite {1}Hn2; case => FF _.
move: (dliftA y2); rewrite -(@FF _ (dliftA x2)).
case/iimageP => g Hg Hg1.
case Pm: (odd_perm g); last first.
  exists g; first by apply/kerP => h; rewrite /= odd_permM Pm.
  have ->: x = (dtuple_tl (dtuple_tl x2)) by rewrite !dtuple_tl_add.
  by rewrite -!naction_tl -Hg1 !dtuple_tl_add.
pose (g1:= transperm b1 b2); exists (g * g1) => [/= |].
  apply/kerP => h; rewrite !odd_permM Pm odd_transp.
  by case/andP: (Hb2) => ->.
have ->: x = (dtuple_tl (dtuple_tl x2)) by rewrite !dtuple_tl_add.
rewrite act_morph -!naction_tl -Hg1.
have Fy3: ~~ dtuple_in b2 y.
  rewrite /dtuple_in /distinctb; case: (y) (Hb1) (Hb2); case => /= v _ _ _.
  by case/andP.
pose y3 := dtuple_add Fy3; have Fy4: ~~ dtuple_in b1 y3.
  rewrite /y3 /dtuple_in /distinctb /=.
  case: (y) (Fy3) (Hb1) (Hb2) => [[v]] /= _ _ _ HH.
  by case/andP => HH1 HH2; apply/norP; split; rewrite // eq_sym.
pose y4 := dtuple_add Fy4.
suff ->: naction (perm_act d) (n -2 + 1 + 1) y2 g1 = y4 by rewrite !dtuple_tl_add.
apply: (dtuple_hd_tl (x:= a1)).
  rewrite dtuple_hd_add naction_hd /= /to /g1 // dtuple_hd_add.
  by case: (transpP b1 b2 b2).
rewrite dtuple_tl_add naction_tl dtuple_tl_add.
apply: (dtuple_hd_tl (x:= a1)).
  rewrite dtuple_hd_add naction_hd /= /to /g1 // dtuple_hd_add.
  by case: (transpP b1 b2 b1).
rewrite dtuple_tl_add naction_tl dtuple_tl_add.
case: (y) (Hb1) (Fy3); case.
rewrite /dtuple_in /distinctb /setC /= => z Hz Hz0 Hz1 Hz2.
apply/val_eqP; rewrite /set1 /=; apply/eqP.
elim: (z) Hz1 Hz2 =>  [|a z1 Hrec] //=.
case/norP => Hz3 Hz4; case/norP => Hz5 Hz6.
congr Adds; last by exact: Hrec.
by rewrite /to /g1; case: (transpP b1 b2 a) Hz3 Hz5 => // ->; rewrite eq_refl.
Qed.

Lemma perm_act_faithful: faithful (perm_act d) alt (setA d).
Proof.
apply/faithfulP => x H.
apply /eqP; apply/ perm_act1P.
by move=> y; move: (H y); case.
Qed.

End PermutationParity.

Lemma simple_alt_1: forall d: finType, card (setA d) <= 3 -> simple (alt d).
Proof.
move=> d; rewrite leq_eqVlt; case/orP => Hcard; last first.
  have F1: card (alt d) = 1%N by
    (rewrite ltnS leq_eqVlt in Hcard; case/orP: Hcard => Hcard); 
     [rewrite card_alt (eqP Hcard) | rewrite card_alt0].
  apply/simpleP => K Hs Hd1 Hn; apply/subset_eqP.
  apply/andP; split; apply/subsetP => x; last first.
  move/eqP => <-; exact: group1.
  move=> Kx; move: (subset_leq_card Hs).
  by rewrite F1 (cardD1 1) group1 (cardD1 x) /setD1 Kx; case: (_ == _).
have F1: card (alt d) = 3%N by rewrite card_alt (eqP Hcard).
apply/simpleP => K Hs Hd1 Hn; apply/subset_eqP.
apply/andP; split; apply/subsetP => x; last first.
move/eqP => <-; exact: group1.
move=> Kx; move: (subset_leq_card Hs).
have alt_x: alt d x by rewrite (subsetP Hs).
case diff_1_x: (1 == x) => //.
case Ey: (set0b (setD1 (setD1 (alt d) 1) x)).
  rewrite/set0b in Ey; move: F1.
  by rewrite (cardD1 1) group1 (cardD1 x) (eqP Ey) /setD1 diff_1_x alt_x.
case/set0Pn: Ey => y ; case/andP => diff_x_y; case/andP=> diff_1_y alt_y.
have alt_xy: alt d (x * y) by apply: groupM.
move: (F1); rewrite (cardD1 1) (cardD1 x) (cardD1 y) (cardD1 (x * y)) /setD1
                  group1 alt_x alt_y alt_xy diff_1_x diff_1_y !diff_x_y.
case E0: (y == x * y).
  case/negP: diff_1_x; have ->: x = (x * y) * y^-1 by gsimpl.
  by rewrite -(eqP E0) mulgV.
case E1: (x == x * y).
  case/negP: diff_1_y; have ->: y = x^-1 * (x * y) by gsimpl.
  by rewrite -(eqP E1)  mulVg.
case E2: (1 == x * y) => //.
case: Hd1 => z; move: F1.
rewrite (cardD1 1) (cardD1 x) (cardD1 y) (cardD1 z) /setD1 group1 diff_1_x
        diff_1_y diff_x_y alt_x alt_y.
case Z0: (1 == z); first by rewrite -(eqP Z0) !group1.
case Z1: (x == z); first by rewrite -(eqP Z1) Kx.
case Z2: (y == z).
  rewrite -(eqP Z2) alt_y; have ->: y = x^-1 * (x * y) by gsimpl.
  by rewrite groupM // -?(eqP E2) // groupV Kx.
case alt_z: (alt d z) => //.
by move => _; apply/negP => Kz; case/negP: alt_z; apply: (subsetP Hs).
Qed.

Lemma transpD: forall (d: finType) (x y z: d), x != z -> y != z -> transp x y z = z.
by move => d1 x y z D1 D2; case transpP => // HH;
   [case/negP: D1 | case/negP: D2]; rewrite HH.
Qed.

Lemma transpCom: forall (d: finType) (x y z t: d), uniq (Seq x y z t) -> 
 commute (transp x y) (transp z t).
move=> d x y z t Uniq; apply/conjg_fpP.
rewrite /conjg_fp transpJ !transpD //.
- by case/and5P: Uniq => _; rewrite /= /setU1 /=; case: (_ == _).
- by case/and5P: Uniq => _; rewrite /= /setU1 /=; case: (t == _) => //; rewrite orbT.
- by case/and5P: Uniq; rewrite /= /setU1 /=; case: (z == _) => //; rewrite orbT.
- by case/and5P: Uniq; rewrite /= /setU1 /=; case: (t == _) => //; rewrite !orbT.
Qed.

(* Simplication of trans p *)
Ltac transp_tac_aux t := match t with
  fun_of_perm _  (fun_of_perm ?X ?Y) => 
     let z := constr: (fun_of_perm X Y) in (transp_tac_aux z) 
| fun_of_perm (transperm ?X ?Y) ?Z => 
        (rewrite (@transpD _ X Y Z) //; try (rewrite eq_sym; done))
end.

Ltac transp_tac :=
  rewrite transpR || rewrite transpL ||
  match goal with |- context [fun_of_perm ?X ?Y] =>
     let z := constr: (fun_of_perm X Y) in (transp_tac_aux z)
  end.

(* use of injectivity of permutation to remove impossible case *)
Ltac iperm_tac := match goal with 
H: ?X = fun_of_perm ?U ?Y,
H1: ?X = fun_of_perm ?U ?Z |- _ => rewrite H in H1;
match goal with 
D: is_true (negb (set1 Y Z)) |- _ => 
 by case/negP: D; apply/eqP; apply: (@inj_act _ _ (perm_act _) U)
| D: is_true (negb (set1 Z Y)) |- _ => 
 by case/negP: D; apply/eqP; apply: (@inj_act _ _ (perm_act _) U)
end
end.

Lemma not_simple_alt_4: forall d: finType, card (setA d) = 4 -> ~ (simple (alt d)).
Proof.
move => d card_d.
(* We exhibit the element of d. *)
case Ex1: (set0b (setA d)).
  by move: card_d; rewrite /set0b in Ex1; rewrite (eqP Ex1).
case/set0Pn: Ex1 => x1 d_x1.
case Ex2: (set0b (setD1 (setA d) x1)).
  by move: card_d; rewrite /set0b in Ex2; rewrite (cardD1 x1) d_x1 (eqP Ex2).
case/set0Pn: Ex2 => x2; case/andP => diff_x1_x2 d_x2.
case Ex3: (set0b (setD1 (setD1 (setA d) x1) x2)).
  move: card_d; rewrite /set0b in Ex3; 
  by rewrite (cardD1 x1) (cardD1 x2) /setD1 d_x1 d_x2 diff_x1_x2 (eqP Ex3).
case/set0Pn: Ex3 => x3; case/andP => diff_x2_x3; case/andP => diff_x1_x3 d_x3.
case Ex4: (set0b (setD1 (setD1 (setD1 (setA d) x1) x2) x3)).
  move: card_d; rewrite /set0b in Ex4; 
  by rewrite (cardD1 x1) (cardD1 x2) (cardD1 x3) /setD1 
             d_x1 d_x2 d_x3 diff_x1_x2 diff_x1_x3 diff_x2_x3 (eqP Ex4).
case/set0Pn: Ex4 => x4; case/andP => diff_x3_x4; case/andP => diff_x2_x4;
                        case/andP => diff_x1_x4 d_x4.
have d_inv: forall z, [|| x1 == z, x2 == z, x3 == z | x4 == z].
  move => z; move: card_d.
  rewrite (cardD1 x1) (cardD1 x2) (cardD1 x3) (cardD1 x4) (cardD1 z) /setD1
          diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4
          d_x1 d_x2 d_x3 d_x4 /setA.
  by do 4 (case: (_ == _) => //).
(* Here are the elements of the normal subgroup *)
pose el1 := (transp x1 x2) * (transp x3 x4).
pose el2 := (transp x1 x3) * (transp x2 x4).
pose el3 := (transp x1 x4) * (transp x2 x3).
pose S := {: 1} :|: {: el1} :|: {: el2}:|: {: el3}.
have Sel1: S el1 by rewrite /S !s2f eq_refl !orbT.
have Sel2: S el2 by rewrite /S !s2f eq_refl !orbT.
have Sel3: S el3 by rewrite /S !s2f eq_refl !orbT.
(* It is a group *)
have group_S: group_set S.
  (* Multiplication table *)
  have el12: el1 * el1 = 1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM perm1;
      repeat transp_tac.
  have el22: el2 * el2 = 1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM perm1;
      repeat transp_tac.
  have el32: el3 * el3 = 1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM perm1;
      repeat transp_tac.
  have el1_el2: el1 * el2 = el3.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el2_el1: el2 * el1 = el3.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el1_el3: el1 * el3 = el2.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el3_el1: el3 * el1 = el2.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el2_el3: el2 * el3 = el1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el3_el2: el3 * el2 = el1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  rewrite /group_set {1}/S.
  rewrite /isetU !s2f eq_refl; apply/subsetP => x.
  case/smulgP => elx ely Sx Sy ->.
  move: Sx Sy; rewrite {1}/S /isetU !s2f.
  rewrite -!orb_assoc; case/or4P => E0; rewrite -{E0}(eqP E0) ?mul1g //;
    case/or4P => E0; rewrite -{E0}(eqP E0) ?mulg1 ?el12 ?el22 ?el32
     ?el1_el2 ?el2_el1 ?el1_el3 ?el3_el1 ?el2_el3 ?el3_el2 ?eq_refl ?orbT //.
(* It is a subset of alt *)
have S_subset: subset S (alt d).
  apply/subsetP => x.
  rewrite {1}/S /isetU 7!s2f -!orb_assoc; case/or4P => E0; 
     rewrite -{E0}(eqP E0) ?group1 //; apply/altP;
     rewrite /even_perm odd_permM !odd_transp 
             ?diff_x1_x2 ?diff_x1_x3 ?diff_x1_x4 ?diff_x2_x3 
             ?diff_x2_x4 ?diff_x3_x4 //.
(* It is normal *)
have S_norm: S <| alt d.
  have Sel1t: S (transp x3 x4 * transp x1 x2).
    suff <-: el1 = transp x3 x4 * transp x1 x2 by done.
    apply/eqP; apply: transpCom.
    move: diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4.
    rewrite /= /setU1 ?(eq_sym x2 x1) ?(eq_sym x3 x1)?(eq_sym x4 x1)
           ?(eq_sym x3 x2)  ?(eq_sym x4 x2) ?(eq_sym x4 x3);
    do 6 (case: (_ == _) => //).
  have Sel2t: S (transp x2 x4 * transp x1 x3).
    suff <-: el2 = transp x2 x4 * transp x1 x3 by done.
    apply/eqP; apply: transpCom.
    move: diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4.
    rewrite /= /setU1 ?(eq_sym x2 x1) ?(eq_sym x3 x1)?(eq_sym x4 x1)
         ?(eq_sym x3 x2)  ?(eq_sym x4 x2) ?(eq_sym x4 x3);
    do 6 (case: (_ == _) => //).
  have Sel3t: S (transp x2 x3 * transp x1 x4).
    suff <-: el3 = transp x2 x3 * transp x1 x4 by done.
    apply/eqP; apply: transpCom.
    move: diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4.
    rewrite /= /setU1 ?(eq_sym x2 x1) ?(eq_sym x3 x1)?(eq_sym x4 x1)
         ?(eq_sym x3 x2)  ?(eq_sym x4 x2) ?(eq_sym x4 x3);
    do 6 (case: (_ == _) => //).
  apply/normalP => x Hx; apply norm_sconjg.
  rewrite /normaliser /= s2f; apply/subsetP =>y.
  rewrite /sconjg s2f.
  by rewrite {1}/S /isetU 7!s2f -!orb_assoc; case/or4P => E0;
  move: (conjgKv x y); rewrite /cancel => <-; rewrite -(eqP E0) {E0};
  first (by rewrite conj1g /S !s2f eq_refl);
   rewrite /el1 /el2 /el3 conjg_mul !transpJ;
    case/or4P: (d_inv (x x1)); move/eqP => Ex1; rewrite -Ex1;
    case/or4P: (d_inv (x x2)); move/eqP => Ex2; rewrite -Ex2; try iperm_tac;
    case/or4P: (d_inv (x x3)); move/eqP => Ex3; rewrite -Ex3; (try iperm_tac);
    case/or4P: (d_inv (x x4)); move/eqP => Ex4; rewrite -Ex4; (try iperm_tac);
     rewrite ?(transpC x4) ?(transpC x2 x1) ?(transpC x3 x2) ?(transpC x3 x1)
             ?(transpC x4 x3) -/el1 -/el2 -/el3.
(* But it is not all alt *)
have S_not_all: ~ S =1 alt d.
  pose el4:= transp x1 x2 * transp x2 x3.
  have alt_el4: alt d el4.
   apply/altP; rewrite /even_perm odd_permM !odd_transp.
   by rewrite diff_x1_x2 diff_x2_x3.
  move /(_ el4); rewrite alt_el4; move/idP.
  rewrite /S /= !s2f.
  have el4_1: el4 x1 = x3  by rewrite /el4 permM; repeat transp_tac.
  have el4_2: el4 x2 = x1 by rewrite /el4 permM; repeat transp_tac.
  case E1: (_ == _); last clear E1.
    by case/negP: (diff_x1_x3); rewrite -el4_1 -(eqP E1) perm1.
  case E1: (_ == _); last clear E1.
    case/negP: (diff_x2_x3); rewrite -el4_1 -(eqP E1).
    by rewrite /el1 permM; repeat transp_tac.
  case E1: (_ == _); last clear E1.
    case/negP: (diff_x1_x4); rewrite -el4_2 -(eqP E1).
    by rewrite /el2 permM; repeat transp_tac.
  case E1: (_ == _) => //.
  case/negP: (diff_x3_x4); rewrite -el4_1 -(eqP E1).
  by  rewrite /el3 permM; repeat transp_tac.
move /simpleP ; move /(_ (Group group_S) S_subset S_not_all S_norm el1).
rewrite Sel1; case E0: (_ == _); move/eqP: E0 => // E0 _.
have: el1 x1 == x2 by rewrite /el1 permM; repeat transp_tac.
by apply/negP; rewrite -E0 perm1.
Qed.

(*
Axiom ok: forall P, P.

Lemma simple_alt5: forall d: finType, card (setA d) = 5 -> simple (alt d).
Proof.
move => d Hd; apply/simpleP => H Hh1 Hh2 Hh3.
case E1: (set0b (setA d)); first by rewrite /set0b Hd in E1.
case/set0Pn: E1 => x Hx.
have F1: card (alt d) = 60.
  have ->: 60 = divn (fact 5) 2 by done.
  by rewrite -Hd -card_alt ?divn_mulr // Hd.
have F2 := alt_trans d; rewrite Hd in F2.
have F3 := ntransitive1 ((refl_equal _): 0 < 3) F2.
have F4 := ntransitive_primitive ((refl_equal _): 1 < 3) F2.
case: (prim_trans_norm F3 F4 Hh1 Hh3) => F5.
  move => z; apply/idP/eqP => Hz; last by rewrite -Hz group1.
  apply/eqP; move: (perm_act_faithful d); rewrite /faithful.
  rewrite (cardD1 1) (cardD1 z) akernel1 /setD1.
  case: (1 == _); case E1: (akernel _ _ _ z) => //.
  by case/idP: E1; apply: (subsetP F5).
have F6: dvdn 5 (card H) by rewrite -Hd; apply: (trans_div Hx F5).
have F7: dvdn 4 (card H).
  have F7: card (setD1 (setA d) x) = 4.
    apply/eqP; rewrite -(eqn_addl 1) /=; apply/eqP.
    by move: Hd; rewrite (cardD1 x) Hx.
  case E1: (set0b (setD1 (setA d) x)); first by rewrite /set0b F7 in E1.
  case/set0Pn: E1 => y Hy.
  pose K := group_stab (perm_act d) H x.
  have F8: subset K H by apply: subset_stab.
  pose Gx := group_stab (perm_act d) (alt d) x.
  have F9: ntransitive (perm_act d) Gx (setD1 (setA d) x) (3 - 1) by apply:  stab_ntransitive.
  have F10: transitive (perm_act d) Gx (setD1 (setA d) x) by apply:  ntransitive1 F9.
  have F11: primitive (perm_act d) Gx (setD1 (setA d) x) by apply: ntransitive_primitive F9.
  have F12: subset K Gx.
    apply/subsetP=> g; case/stabilizerP => Hg Hperm.
    by apply/stabilizerP; split => //; apply: (subsetP Hh1).
  have F13: K <| Gx.
    apply/subsetP => g; case/stabilizerP => Hg Hperm.
    rewrite /normaliser s2f; apply/subsetP => g1 /=.
    rewrite /sconjg s2f; case/stabilizerP => Hg1 Hperm1.
    apply/stabilizerP; split.
      by move/normalP: Hh3; move/(_ g Hg) => <-; rewrite s2f.
    move: Hperm1; rewrite !act_morph invgK Hperm -act_morph => Hperm1.
    apply: (@inj_act _ _ (perm_act d) g^-1).
    by rewrite -{2}Hperm -!act_morph mulgV act_1.
  case: (prim_trans_norm F10 F11 F12  F13) => Ksub; last first.
    apply: dvdn_trans (group_dvdn F8). 
    by rewrite -F7; apply: (@trans_div _ _ (perm_act d) _ _ _ Hy).
  have F14: faithful (perm_act d) Gx (setD1 (setA d) x).
    apply/faithfulP => g Hg.
    apply: (faithfulP _ _ _ (perm_act_faithful d)) => z Hz.
    case: (Hg _ Hy); case/stabilizerP => Hag Hx1 Hy1; split => //.
    case E1: (x == z); first by rewrite -(eqP E1).
    by case: (Hg z); rewrite // /setD1 E1.
  have Hreg: forall g (z: d), H g -> g z = z -> g = 1.
    have F15: forall g, H g -> g x = x -> g = 1.
      move => g Hg Hgx.
      have F15: card K <= 1.
        rewrite /faithful /= in F14; rewrite -(eqP F14).
        by apply: subset_leq_card.
      have F16: K g by  apply/stabilizerP; split.
      apply: sym_equal; apply/eqP; move: F15; rewrite (cardD1 1) group1 (cardD1 g) /setD1 F16.
      by case (1 == g).   
    move=> g z Hg Hgz.
    have: (setA d x) by done.
    rewrite -(F3 z) //; case /iimageP => g1 Hg1 Hg2.
    apply: (mulg_injl g1^-1); apply: (mulg_injr g1); gsimpl.
    apply: F15; first by rewrite -sconjgE (normalP _ _ Hh3) // groupV.
    change (perm_act d x (g1^-1 * g * g1) = x).
    by rewrite Hg2 -act_morph; gsimpl; rewrite act_morph {2}/perm_act /to /= Hgz.
  clear K F8 F12 F13 Ksub F14.
Fail.

*)


  
Coercion odd_perm : permType >-> bool.
