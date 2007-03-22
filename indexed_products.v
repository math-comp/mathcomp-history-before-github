Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp.

Section indexed_products.

Variables (R:Type)(mulR : R -> R -> R)(e:R).

Notation "x * y" := (mulR x y).
Notation "1" := e.
Hypotheses
  (mulP : forall x1 x2 x3, x1 * (x2 * x3) = (x1 * x2) * x3)
  (mulC : forall x1 x2, x1 * x2 = x2 * x1)
  (unitP : forall x, 1 * x = x).

Section iprod.
Variables (d:finType)(a:set d)(f:d->R).

Definition iprod := foldr (fun x => mulR (f x)) 1 (filter a (enum d)).

End iprod.

Lemma iprod0 : forall (d:finType)(f:d->R), iprod d set0 f = 1.
Proof. by move => d f; rewrite /iprod filter_set0. Qed.

Lemma iprod_1 : forall (d:finType)(a:set d), iprod d a (fun x => 1) = 1.
Proof.
move => d a; rewrite /iprod.
by elim: (filter a (enum d)) => //=; move => x s Hs; rewrite unitP.
Qed.

Lemma eq_iprod_set: forall (d:finType) a b (f:d->R),
  a =1 b -> iprod _ a f = iprod _ b f.
move => d a b N H; rewrite /iprod; elim (enum d) => [| x s Hrec] //=.
by rewrite H; case (b x) => //=; congr mulR.
Qed.

Lemma eq_iprod_f: forall (d:finType) (a:set d) (f g:d->R),
  (forall x, a x -> f x = g x) ->
  iprod _ a f = iprod _ a g.
move => d a f g H; rewrite /iprod.
elim: (enum d) => //=.
by move => x s IHs; case E: (a x) => //=; rewrite H => //; congr mulR.
Qed.

Lemma iprodD1 : forall (d:finType) x (a:set d) (f:d->R),
 a x -> iprod _ a f = f x * iprod _ (setD1 a x) f.
Proof.
move => d x a f.
have F1: setD1 a x =1 setD1 (filter a (enum d)) x.
 by move => x1; rewrite /setD1 filter_enum.
rewrite /iprod (eq_filter F1) -(filter_enum a x).
elim: (enum d) (uniq_enum d) => [| x1 s1 Hrec] //=; rewrite /id.
case/andP; move/negP=>H1 H2.
case E1: (a x1) => /=.
 case/orP => H3.
  rewrite -!(eqP H3) setD11; congr mulR; congr foldr. 
  apply: eqd_filter => x2 Hx2; rewrite /setD1 /setU1.
  case E2: (x1 == x2) => /=; first by case H1; rewrite (eqP E2).
  by rewrite mem_filter /setI Hx2 andbT.
 have F2: setD1 (setU1 x1 (filter a s1)) x x1.
  rewrite mem_filter in H3; case/andP: H3 => H3 H4.
  rewrite /setD1 /setU1 mem_filter /setI.
  case E2: (x==x1) => /=; first by case H1; rewrite -(eqP E2).
  by rewrite eq_refl.
 rewrite F2 Hrec //= !mulP; congr mulR; first exact: mulC. 
 congr foldr; apply eqd_filter => x2 Hx2; rewrite /setD1 /setU1.
 case E2: (x==x2)=>//=; rewrite mem_filter /setI.
 case (a x2) => //=; case E3:(x1==x2) => //=; by case H1; rewrite (eqP E3).
move => H3; rewrite Hrec //; congr mulR; congr foldr.
have F2: setD1 (filter a s1) x x1 = false.
by rewrite /setD1 mem_filter /setI E1 /= andbF.
by rewrite F2.
Qed.

Lemma iprod_setU : forall (d:finType)(a b: set d)(f:d->R),
 disjoint a b -> iprod _ (setU a b) f = iprod _ a f * iprod _ b f.
move => d a b f.
elim: {a}(card a) {-2}a (refl_equal (card a)) b => [| n Hrec] a Ha b Hab.
 rewrite (eq_iprod_set _ _ _ _ (card0_eq Ha)) iprod0 unitP.
 have F1: setU a b =1 b by move => x; rewrite /setU (card0_eq Ha).
 by rewrite (eq_iprod_set _ _ _ _  F1).
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (iprodD1 _ x) ?(iprodD1 _ x a) //; last by rewrite /setU Hx.
rewrite -mulP; congr mulR.
have F0: card (setD1 a x) = n. 
 by apply (@addn_injl 1%N); rewrite (add1n n) -Ha (cardD1 x a) Hx.
have F1: setD1 (setU a b) x =1 setU (setD1 a x) b.
 move => x1; rewrite /setD1 /setU.
 case E1: (x == x1) => //=; rewrite /disjoint /set0b in Hab.
 move: (card0_eq (eqP Hab)) => H1. 
 case E2: (b x1) => //; case (H1 x1); by rewrite /setI E2 -(eqP E1) Hx.
rewrite (eq_iprod_set _ _ _ _ F1) Hrec // /disjoint; apply/set0P => x1.
rewrite /setI /setD1.
case E1: (x==x1) => //=. 
rewrite /disjoint /set0b in Hab; move: (card0_eq (eqP Hab)) => H1.
case E2: (a x1) => //=.
by move: (H1 x1); rewrite /setI E2.
Qed.

Lemma iprod_set1 : forall (d:finType)(i:d)(f:d->R),
  iprod _ (set1 i) f = f i.
move => d i f; rewrite /iprod. 
move: (count_set1_uniq i (uniq_enum d)).
rewrite count_filter mem_enum /setA /nat_of_bool.
have H : filter (set1 i) (enum d) i by rewrite filter_enum; apply/set1P.
move: H; case: (filter (set1 i) (enum d)) => //=.
by move => x [|x' s'] //= ; rewrite /setU1 orbF => Heq; rewrite (eqP Heq) mulC unitP.
Qed.

Lemma iprod_mul : forall (d:finType)(a : set d)(f g:d->R),
  iprod d a (fun x => f x * g x) = iprod d a f * iprod d a g.
move => d a f g.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
 by rewrite !(eq_iprod_set _ _ _ _ (card0_eq Ha)) !iprod0.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite !(iprodD1 _ x a) // -(mulP (f x) (iprod d (setD1 a x) f)). 
rewrite (mulP (iprod d (setD1 a x) f)) (mulC (iprod d (setD1 a x) f)) -!mulP -Hrec //.
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.


Lemma iprod_parts : forall (d:finType)(a : set d)(f:d->R)(g:d->d),
 disjoint a (image g a) -> dinjective a g ->
 iprod d (setU a (image g a)) f = iprod d a (fun x => f x * f (g x)).
move => d a f g.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha Hd Hi.
 rewrite (eq_iprod_set _ _ _ _ (card0_eq Ha)) iprod0.
 rewrite (eq_iprod_set d (setU a (image g a)) set0 f); first exact: iprod0.
 move => x; rewrite /setU (card0_eq Ha) /=; apply/imageP.
 by move => [y Hay _]; rewrite (card0_eq Ha) in Hay.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (iprodD1 _ x); last by rewrite /setU; apply/orP;left.
rewrite (iprodD1 _ x a) //= -mulP; congr mulR.
rewrite (iprodD1 _ (g x)).
 congr mulR.
 have F1 :(setD1 (setD1 (setU a (image g a)) x) (g x)) =1
    setU (setD1 a x) (image g (setD1 a x)).
  move => y; rewrite /setD1 /setU.
  move/set0Pn: Hd => Hd.
  case E1: (a y) => /=.
   rewrite andbT.
   case E2: (image g (fun y' => (x!=y') && a y') y).
    rewrite orbT; move/imageP: E2 => [w Haw Hfw]; rewrite Hfw.
    apply/andP; split; move/andP: Haw => [Hxw Haw].
     apply/negP; move => Hgxw; case/negP: Hxw. 
     by apply/eqP; apply: Hi => //; apply/eqP.
    apply/negP => Hxgw; case Hd; exists x; rewrite /setI.
    by apply/andP; split => //=; apply/imageP; exists w => //=; apply/eqP.
   have F1 : (g x != y).
    apply/negP => Hgx; move/eqP: Hgx => Hgx; case Hd; exists y; rewrite /setI.
    by apply/andP; split => //=; apply/imageP; exists x =>//=.
   by rewrite F1 orbF.
   rewrite andbF /=.
   apply/andP/imageP.
   move => [Hgxy H']; move/andP: H' => [Hxy Him]; move/imageP: Him => [w Haw Hwy].
   exists w => //; apply/andP; split => //.
   by apply/negP => Hxw; case/negP: Hgxy; apply/eqP; rewrite Hwy; congr g; apply/eqP.
  move => [w H' Hwy]; move/andP: H' => [Hxw Haw]; split.
   rewrite Hwy; apply/negP => Hgxy; case/negP: Hxw.
   by apply/eqP; apply: Hi => //; apply/eqP.
  apply/andP;split.
   apply/negP;move => Hxy; apply Hd;exists y; rewrite /setI; apply/andP;split.
    by rewrite -(eqP Hxy).
   by apply/imageP; exists w => //.
  by apply/imageP; exists w => //.
  rewrite (eq_iprod_set _ _ _ _ F1); apply Hrec.
   by apply: (@addn_injl 1%N); rewrite (add1n n) -Ha; rewrite (cardD1 x a) Hx => //=.
  apply/set0Pn; rewrite /setD1 /setI; move => [x0 H']; move/andP: H' => [Hdx Hidx].
  move/andP: Hdx => [_ Hax0].
  move/imageP: Hidx => [w Haw Hgw]; move/andP: Haw => [_ Haw].
  case/set0Pn: Hd; exists x0; rewrite /setI; apply/andP; split => //.
  by apply/imageP; exists w => //.
 rewrite /dinjective /setD1; move => w w' Hw Hw'.
 move/andP: Hw => [_ Hw]; move/andP:Hw' => [_ Hw'].
 by apply Hi => //.
rewrite /setD1 /setU; apply/andP; split.
 apply/negP => Hxg; move/eqP: Hxg => Hxg.
 case/set0Pn: Hd; exists x; rewrite /setI; apply/andP; split => //.
 by apply/imageP; exists x => //.
apply/orP;right;apply/imageP; exists x => //.
Qed.

Section distr.

Variable m' : R -> R -> R.
Hypothesis distr : forall x y z, m' (mulR x y) z = mulR (m' x z) (m' y z).
Hypothesis m'1x : forall x, m' 1 x = 1.

Lemma i_prod_distr :
  forall (d:finType) (a:set d) alpha f,
     iprod _ a (fun x => m' (f x) alpha) = m' (iprod _ a f) alpha.
move => d a alpha f.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
 by rewrite !(eq_iprod_set _ _ _ _ (card0_eq Ha)) !iprod0 m'1x.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (iprodD1 _ x) //=; rewrite (iprodD1 _ x a) //=. 
rewrite distr; congr mulR; apply Hrec. 
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.

End distr.

Lemma image_set0 : forall (d d':finType)(g:d->d'), image (d:=d) g set0 =1 set0.
by move => d d' g x; case E: (image g set0 x) => //; move/imageP: E=> [y H _].
Qed.

Lemma image_eq : forall (d d':finType)(a b:set d)(g f:d->d'), a =1 b ->
     g =1 f -> image g a =1 image f b.
move => d d' a b g f Ha Hg x; apply/imageP/imageP; move => [y Hin Heq].
 by exists y; [rewrite -Ha | rewrite -Hg].
by exists y; [rewrite Ha | rewrite Hg].
Qed.

Lemma i_prod_image :
  forall (d:finType) (a:set d) (g:d->d) f, dinjective a g ->
   iprod _ (image g a) f = iprod _ a (fun x => f (g x)).
move => d a.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha g f Hg.
 have F1: a =1 set0 by apply card0_eq.
 have F2: image g a =1 set0. 
  by move => x; rewrite (image_eq _ _ a set0 g g) //; rewrite (image_set0 d d g x).
 by rewrite (eq_iprod_set d _ _ _ F1) (eq_iprod_set d _ _ _ F2) !iprod0.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (iprodD1 _ x a) => //.
rewrite (iprodD1 _ (g x)); last by apply/imageP; exists x.
congr mulR.
have F3: setD1 (image g a) (g x) =1 image g (setD1 a x).
 move => y;apply/andP/imageP.
  move => [Hngx Hin]; move/imageP: Hin => [z Hin Heq];exists z =>//.
  apply/andP; split => //; apply/negP; move => Heq'. 
  by rewrite (eqP Heq') in Hngx; case/negP: Hngx; rewrite Heq.
 move => [z Hin Heq]; move/andP: Hin => [Hzx Hin]; split.
  apply/negP;move/eqP => Heq'.
  by move/negP: Hzx => H; case H; apply/eqP; apply Hg => //; rewrite -Heq.
 by apply/imageP; exists z.
rewrite (eq_iprod_set d _ _ _ F3); apply Hrec => //.
 by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
move => x' y' Hx' Hy' Heq; move/andP:Hx'=>[_ Hx']; move/andP:Hy'=>[_ Hy']. 
by apply Hg => //.
Qed.

End indexed_products.
