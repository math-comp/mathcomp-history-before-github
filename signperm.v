Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp action.

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

End PermutationParity.