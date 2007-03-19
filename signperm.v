Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp action.

Import Prenex Implicits.

Section sign.

Variables (d:finType).

Section EqProd.

Variables d1 d2 : eqType.

Definition pair_of_eq_pair p := let: EqPair x1 x2 := p in (x1 : d1, x2 : d2).

Definition eq_pair_of_pair p := let: (x1, x2) := p in EqPair (x1 : d1) (x2 : d2).

Lemma eqpairK : cancel eq_pair_of_pair pair_of_eq_pair.
Proof. by case. Qed.

Canonical Structure pair_eqType := EqType (can_eq eqpairK).

End EqProd.

Canonical Structure prod_finType.

Canonical Structure pair_finType (d1 d2 : finType) :=
   FinType (can_uniq (@eqpairK d1 d2)).

Definition ordered_pair u := index (fst u) (enum d) < index (snd u) (enum d).

Notation Local op := ordered_pair.

Definition flip_pair A u : A * A := let: (x, y) := u in (y, x).

Notation Local fl := (@flip_pair d).

Lemma flip_pairK : involutive fl.
Proof. by case. Qed.
Notation Local flK := flip_pairK.
Definition flip_pair_inj := inv_inj flK.
Notation Local flI := flip_pair_inj.

Lemma image_flip_pair : forall u A, image fl A u = A (fl u).
Proof. by move=> u A; rewrite -{1}(flK u) (image_f flI). Qed.
Notation Local im_fl := image_flip_pair.

Lemma ordered_pair_flip : forall p, op (fl p) = ((fl p != p) && ~~ op p).
Proof.
case=> x y /=; rewrite /op ltn_neqAle -leqNgt; congr andb; congr negb.
rewrite {2}/set1 /= {2}/set1 /= (eq_sym y) andbb; apply/eqP/eqP=> [|-> //].
by rewrite -{2}(sub_index x (mem_enum y)) => ->; rewrite sub_index // mem_enum.
Qed.
Notation Local op_fl := ordered_pair_flip.

Definition perm_pair (sigma : permType d) u :=
  let: (x, y) := u in (sigma x, sigma y).
Notation Local p2 := perm_pair.

Lemma perm_flip_pair : forall sigma u, p2 sigma (fl u) = fl (p2 sigma u).
Proof. by move=> ? []. Qed.
Notation Local p2_fl := perm_flip_pair.

Lemma perm_pair1 : forall u, p2 1 u = u. 
Proof. by move=> [x y]; rewrite /= /fun_of_perm !g2f. Qed.
Notation Local p21 := perm_pair1.
 
Lemma perm_pairM : forall sigma tau u, p2 (sigma * tau) u = p2 tau (p2 sigma u).
Proof. by move=> s t [x y] /=; rewrite /fun_of_perm !g2f. Qed.
Notation Local p2M := perm_pairM.

Lemma perm_pairK : forall sigma, cancel (p2 sigma) (p2 sigma^-1).
Proof. by move=> sigma u; rewrite -p2M mulgV p21. Qed.
Notation Local p2K := perm_pairK.
Definition perm_pair_inj sigma := can_inj (p2K sigma).
Notation Local p2I := perm_pair_inj.

Definition inversion sigma u := op (fl (p2 sigma u)).
Notation Local ivn := inversion.

Definition perm_signature sigma := odd (card (setI op (ivn sigma))).
Notation Local eps := perm_signature.

Lemma image_perm_pair : forall sigma A u, image (p2 sigma) A u = A (p2 sigma^-1 u).
Proof. by move=> s A u; rewrite -{1}(p2K s^-1 u) invgK (image_f (p2I s)). Qed.
Notation Local im_p2 := image_perm_pair.

Lemma perm_signatureM : forall sigma tau, eps (sigma * tau) = eps sigma (+) eps tau.
Proof.
move=> s t; rewrite /eps -(cardIC (ivn s)); symmetry; rewrite -(cardIC (ivn (s * t))).
rewrite addbC -(card_image (p2I s^-1)) -(cardIC op) !odd_addn.
set n1 := card (setI _ (setC _)); set n2 := card (setI _ (setC _)).
have -> : n1 = n2.
  rewrite /n2 -(card_image flI); apply: eq_card => u /=; rewrite /setI /setC im_fl im_p2.
  rewrite invgK /ivn !p2_fl !flK -p2M !op_fl -p2_fl (inj_eq (@p2I _)) -!andbA; do !bool_congr.
rewrite addbCA addKb; congr addb; congr odd; apply: eq_card=> u; rewrite /= /setI /setC.
  by rewrite -!andbA; do !bool_congr.
rewrite im_p2 invgK /ivn -p2M !op_fl -!p2_fl !(inj_eq (@p2I _)).
case: (_ != u); rewrite ?andbF //= negbK -!andbA; do !bool_congr.
Qed.
Notation Local epsM := perm_signatureM.

Lemma perm_signature1 : eps 1 = false.
Proof. by rewrite -[1]mulg1 epsM addbb. Qed.
Notation Local eps1 := perm_signature1.

Lemma perm_signatureV : forall sigma, eps sigma^-1 = eps sigma.
Proof. by move=> sigma; rewrite -{2}(mulgK sigma sigma) !epsM addbb. Qed.
Notation Local epsV := perm_signatureV.

Lemma perm_signatureJ : forall sigma tau, eps (sigma ^ tau) = eps sigma.
Proof. by move=> *; rewrite /conjg !epsM epsV addbC addbA addbb. Qed.

CoInductive transperm_spec x y z : d -> Type :=
| TranspermFirst : z = x -> transperm_spec x y z y
| TranspermSecond : z = y -> transperm_spec x y z x
| TranspermNone : z <> x -> z <> y -> transperm_spec x y z z.

Lemma transpermP : forall x y z, transperm_spec x y z (transperm x y z).
Proof.
move=> x y z; rewrite /fun_of_perm g2f /transpose; do 2?case: eqP => /=; constructor; auto.
Qed.

Lemma signature_transperm : forall x y, eps (transperm x y) = (x != y).
Proof.
move=> x y; move: (transperm x y) (transpermP x y) => t tP.
have tK: involutive t by move=> z; do 2![case tP => //] => ->.
have tV: t^-1 = t.
  apply: eq_fun_of_perm => z; have:= p2M 1 t (z, z).
  by rewrite mul1g -(mulVg t) p2M => [[-> _]].
case Dxy: (x == y) => /=.
  rewrite -eps1; congr eps; apply: eq_fun_of_perm => z.
  by case: (p21 (z, z)) => -> _; case: tP; rewrite (eqP Dxy).
without loss Oxy: x y tP Dxy / op (x, y).
  case Oyx: (op (fl (y, x))) => Wxy; first exact: Wxy Oyx.
  rewrite op_fl {2}/set1 /= {2}/set1 /= eq_sym in Dxy Oyx; rewrite Dxy in Oyx.
  by move/negbEF: Oyx; apply: Wxy Dxy => z; case tP; constructor.
have [Dtx Dty]: t x = y /\ t y = x by split; case tP.
pose A z u := let: (x', y') := u : d * d in set2 x' y' z.
pose B z u := op u && ivn t u && A z u.
have:= congr1 odd (cardUI (B x) (B y)); rewrite !odd_addn.
have->: card (B x) = card (B y); last rewrite addbb.
  rewrite -(card_image (p2I t)) -(card_image flI).
  apply: eq_card => u; rewrite /= /setI im_fl im_p2 tV.
  rewrite /B /ivn !p2_fl flK -{2}tV p2K -!andbA; do !bool_congr.
  by case: u => x' y'; rewrite /A /= /set2 !(inv_eq tK) orbC Dtx.
move/(fun H => canRL H (addKb _)) => /=.
have{tP}->: odd (card (setU (B x) (B y))) = eps t; last move->.
  congr odd; apply: eq_card=> u /=; rewrite /setI /setU /B.
  case: (@andP (op u)) => //=; case; rewrite /ivn op_fl => Ou; case/andP=> _ Otu.
  apply/norP; case; rewrite /A; case: u => [x' y'] /= in Ou Otu *.
  do 2![case/norP; do 2!move/eqP=> ?]; case/negP: Otu; do 2![case tP => //].
rewrite -[true]/(odd 1) -(card1 (x, y)); congr odd.
apply: eq_card => [[x' y']]; rewrite /setI {}/B {}/A /ivn /= /set1 /= /set1 /=.
rewrite /set2 !(eq_sym x) !(eq_sym y); case: eqP => [-> | _] /=.
  by rewrite Dxy; case: eqP => [->|_]; [rewrite Dtx Dty Oxy | rewrite !andbF].
apply/and3P; case; case/andP=> _; move/eqP=> -> Oxx'; rewrite Dxy orbF; move/eqP=> Dx'.
by rewrite Dx' -(flK (y, x)) op_fl /= Oxy andbF in Oxx'.
Qed.

End sign.