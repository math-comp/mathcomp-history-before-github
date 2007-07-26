Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

Lemma iprod0 : forall (d:finType)(f:d->R), iprod set0 f = 1.
Proof. by move => d f; rewrite /iprod filter_set0. Qed.

Lemma iprod_1 : forall (d:finType)(a:set d), iprod a (fun x => 1) = 1.
Proof.
move => d a; rewrite /iprod.
by elim: (filter a (enum d)) => //=; move => x s Hs; rewrite unitP.
Qed.

Lemma eq_iprod_set: forall (d:finType) a b (f:d->R),
  a =1 b -> iprod a f = iprod b f.
Proof.
move => d a b N H; rewrite /iprod; elim (enum d) => [| x s Hrec] //=.
by rewrite H; case (b x) => //=; congr mulR.
Qed.

Lemma eq_iprod_f: forall (d:finType) (a:set d) (f g:d->R),
  (forall x, a x -> f x = g x) ->
  iprod a f = iprod a g.
Proof.
move => d a f g H; rewrite /iprod.
elim: (enum d) => //=.
by move => x s IHs; case E: (a x) => //=; rewrite H => //; congr mulR.
Qed.

Lemma iprodD1 : forall (d:finType) x (a:set d) (f:d->R),
 a x -> iprod a f = f x * iprod (setD1 a x) f.
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
 disjoint a b -> iprod (setU a b) f = iprod a f * iprod b f.
move => d a b f.
elim: {a}(card a) {-2}a (refl_equal (card a)) b => [| n Hrec] a Ha b Hab.
 rewrite (eq_iprod_set _ (card0_eq Ha)) iprod0 unitP.
 have F1: setU a b =1 b by move => x; rewrite /setU (card0_eq Ha).
 by rewrite (eq_iprod_set _  F1).
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1 _ x) ?(@iprodD1 _ x a) //; last by rewrite /setU Hx.
rewrite -mulP; congr mulR.
have F0: card (setD1 a x) = n. 
 by apply (@addn_injl 1%N); rewrite (add1n n) -Ha (cardD1 x a) Hx.
have F1: setD1 (setU a b) x =1 setU (setD1 a x) b.
 move => x1; rewrite /setD1 /setU.
 case E1: (x == x1) => //=; rewrite /disjoint /set0b in Hab.
 move: (card0_eq (eqP Hab)) => H1. 
 case E2: (b x1) => //; case (H1 x1); by rewrite /setI E2 -(eqP E1) Hx.
rewrite (eq_iprod_set _ F1) Hrec // /disjoint; apply/set0P => x1.
rewrite /setI /setD1.
case E1: (x==x1) => //=. 
rewrite /disjoint /set0b in Hab; move: (card0_eq (eqP Hab)) => H1.
case E2: (a x1) => //=.
by move: (H1 x1); rewrite /setI E2.
Qed.

Lemma iprod_set1 : forall (d:finType)(i:d)(f:d->R),
  iprod (set1 i) f = f i.
move => d i f; rewrite /iprod. 
move: (count_set1_uniq i (uniq_enum d)).
rewrite count_filter mem_enum /setA /nat_of_bool.
have H : filter (set1 i) (enum d) i by rewrite filter_enum; apply/set1P.
move: H; case: (filter (set1 i) (enum d)) => //=.
by move => x [|x' s'] //= ; rewrite /setU1 orbF => Heq; rewrite (eqP Heq) mulC unitP.
Qed.

Lemma iprod_mul : forall (d:finType)(a : set d)(f g:d->R),
  iprod a (fun x => f x * g x) = iprod a f * iprod a g.
move => d a f g.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
 by rewrite !(eq_iprod_set _ (card0_eq Ha)) !iprod0.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite !(@iprodD1 _ x a) // -(mulP (f x) (iprod (setD1 a x) f)). 
rewrite (mulP (iprod (setD1 a x) f)) (mulC (iprod (setD1 a x) f)) -!mulP -Hrec //.
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.


Lemma iprod_parts : forall (d:finType)(a : set d)(f:d->R)(g:d->d),
 disjoint a (image g a) -> dinjective a g ->
 iprod (setU a (image g a)) f = iprod a (fun x => f x * f (g x)).
move => d a f g.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha Hd Hi.
 rewrite (eq_iprod_set _ (card0_eq Ha)) iprod0.
 rewrite (@eq_iprod_set d (setU a (image g a)) set0 f); first exact: iprod0.
 move => x; rewrite /setU (card0_eq Ha) /=; apply/imageP.
 by move => [y Hay _]; rewrite (card0_eq Ha) in Hay.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1 _ x); last by rewrite /setU; apply/orP;left.
rewrite (@iprodD1 _ x a) //= -mulP; congr mulR.
rewrite (@iprodD1 _ (g x)).
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
  rewrite (@eq_iprod_set _ _ _ _ F1); apply Hrec.
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
     iprod a (fun x => m' (f x) alpha) = m' (iprod a f) alpha.
move => d a alpha f.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
 by rewrite !(eq_iprod_set _ (card0_eq Ha)) !iprod0 m'1x.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1 _ x) //=; rewrite (@iprodD1 _ x a) //=. 
rewrite distr; congr mulR; apply Hrec. 
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.

End distr.

(*
Lemma image_set0 : forall (d d':finType)(g:d->d'), image g set0 =1 set0.
by move => d d' g x; case E: (image g set0 x) => //; move/imageP: E=> [y H _].
Qed.

Lemma image_eq : forall (d d':finType)(a b:set d)(g f:d->d'), a =1 b ->
     g =1 f -> image g a =1 image f b.
move => d d' a b g f Ha Hg x; apply/imageP/imageP; move => [y Hin Heq].
 by exists y; [rewrite -Ha | rewrite -Hg].
by exists y; [rewrite Ha | rewrite Hg].
Qed.
*)

Lemma i_prod_image :
  forall (d:finType) (a:set d) (g:d->d) f, dinjective a g ->
   iprod (image g a) f = iprod a (fun x => f (g x)).
move => d a.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha g f Hg.
 have F1: a =1 set0 by apply card0_eq.
 have F2: image g a =1 set0. 
  by move => x; rewrite (@image_eq _ _ a set0 g g) //; rewrite (@image_set0 d d g x).
 by rewrite (@eq_iprod_set d _ _ _ F1) (@eq_iprod_set d _ _ _ F2) !iprod0.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1 _ x a) => //.
rewrite (@iprodD1 _ (g x)); last by apply/imageP; exists x.
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
rewrite (@eq_iprod_set d _ _ _ F3); apply Hrec => //.
 by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
move => x' y' Hx' Hy' Heq; move/andP:Hx'=>[_ Hx']; move/andP:Hy'=>[_ Hy']. 
by apply Hg => //.
Qed.

Lemma i_prod_image2 :
  forall (d d':finType) (a:set d) (g:d->d') f, dinjective a g ->
   iprod (image g a) f = iprod a (fun x => f (g x)).
move => d d' a.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha g f Hg.
 have F1: a =1 set0 by apply card0_eq.
 have F2: image g a =1 set0 
  by move => x; rewrite (@image_eq _ _ a set0 g g) //;
     rewrite (@image_set0 d d' g x).
  by rewrite (@eq_iprod_set d _ _ _ F1) (@eq_iprod_set d' _ _ _ F2) !iprod0.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1 _ x a) => //.
rewrite (@iprodD1 _ (g x)); last by apply/imageP; exists x.
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
rewrite (@eq_iprod_set d' _ _ _ F3); apply Hrec => //.
 by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
move => x' y' Hx' Hy' Heq; move/andP:Hx'=>[_ Hx']; move/andP:Hy'=>[_ Hy']. 
by apply Hg => //.
Qed.

Lemma iprod_injection :
  forall (d d':finType) (a:set d) (a' :set d') (f:d->d') g,
   dinjective a f ->
     iprod a' g =
     iprod (setI a (preimage f a')) (fun x => g (f x)) *
     iprod (setD a' (image f a)) g.
Proof.
move => d d' a a' f g Hinj.
have Hinj' : dinjective (setI a (preimage f a')) f.
 by move => x y Hx Hy; case/andP: Hx => Hx _; case/andP: Hy => Hy _; apply:Hinj.
rewrite -(@i_prod_image2 d d' (setI a (preimage f a')) f g) // -iprod_setU.
 apply: eq_iprod_set; move => x; rewrite /setU /setD.
 case A: (image f a x)=>//=; first (rewrite orbF; case/imageP: A => y B C).
  apply/idP/imageP;first by move=>D;exists y=>//;rewrite /setI B /preimage -C.
  by case => x' Hx' Hf'; case/andP: Hx' => _ Ha'; rewrite Hf'.
 case H': (a' x); first (by rewrite orbT).
 rewrite orbF; apply/idP/imageP; first done.
 by case => y Hy Hf; move/andP: Hy => [Ha Ha']; rewrite -H' Hf.
apply: (@disjoint_trans d' _ (image f a)); rewrite /setI/setD.
 rewrite /subset disjoint_subset;apply/subsetP=>x A; case/imageP:A =>y B C.
 by rewrite /setC negb_involutive; case/andP: B=>B _; apply/imageP; exists y.
by apply/set0P; rewrite /setI //=; move =>x //=; case: (image f a x) => //.
Qed.

Lemma ltn_addr : forall m n p, m < n -> m < n + p.
Proof.
elim=> [|m Hrec] [|n] [|p] //; rewrite ?addn0 //=; try exact (Hrec n (S p)).
Qed.

Lemma ltn_addl : forall m n p, m < n -> m < p + n.
Proof.
elim=> [|m Hrec] [|n] [|p] //; rewrite ?add0n //= => H.
apply: (Hrec (S n) p).
by apply: (@ltn_trans (S m) m (S n)).
Qed.

Definition inj_ord (m n :nat) : (ordinal m) -> (ordinal (m+n)) := 
  fun i => let: (Ordinal x Hx) := i in Ordinal (@ltn_addr x m n Hx).

Definition inj_ord_add (m n : nat) : (ordinal m) -> (ordinal (m+n)).
move=> m n [i Hi].
exists (i + n).
by rewrite ltn_add2r.
Defined.

Lemma inj_inj_ord : forall m n, injective (@inj_ord m n).
Proof.
move=> m n.
case=>//[i Hi] [i' Hi'] //= H.
move/ord_eqP : H => //= H.
by apply/ord_eqP => //=.
Qed.

Lemma inj_inj_ord_add : forall m n, injective (@inj_ord_add m n).
Proof.
move=> m n.
case=>//[i Hi] [i' Hi'] //= H.
move/ord_eqP : H => //= H.
apply/ord_eqP => //=.
by rewrite eqn_addr in H.
Qed.

Lemma inj_ord_image : forall m n i,
  (image (@inj_ord m n) (setA (ordinal_finType m)) ) i = (i < m).
move=> m n i.
case H1:( i < m).
  move/idP: H1 => H1.
  pose ii:= Ordinal H1.
  have H2: (@inj_ord m n) ii = i by apply: ordinal_inj => //.
  rewrite -H2 image_f //; apply: inj_inj_ord.
apply/idP => H2.
move/imageP: H2 => H2.
elim: H2 => ii _ H3.
move: (ordinal_ltn ii) => H4.
have H5: (@inj_ord m n ii) = ii :>nat.
  clear H3 H4; case: ii.
  rewrite / inj_ord //=.
rewrite H3 H5 in H1.
by rewrite H4 in H1.
Qed.

Lemma inj_ord_add_image : forall m n i,
  (image (@inj_ord_add m n) (setA (ordinal_finType m)) ) i = (n <= i).
move=> m n i.
case H1:( n <= i).
  move/idP: H1 => H1.
  have H2: i - n < m.
    case: i H1=> //= [i Hi H1].
    rewrite addnC in Hi.
    rewrite -leq_sub_add in Hi.
    apply: (@leq_trans (S i - n) _ _) => //.
    apply: ltn_sub2r => //.
  pose ii:= Ordinal H2.
  have H3: (@inj_ord_add m n) ii = i .
    by rewrite //=; apply: ordinal_inj => //=; rewrite addnC; apply: leq_add_sub.
  rewrite -H3 image_f //; apply: inj_inj_ord_add.
apply/idP => H2.
move/imageP: H2 => H2.
elim: H2 => ii _ H3.
move: (ordinal_ltn ii) => H4.
have H5: (@inj_ord_add m n ii) = ii + n :>nat.
  clear H3 H4; case: ii.
  rewrite / inj_ord //=.
rewrite H3 H5 //= in H1.
move: (leq_addl ii n) => H6.
by rewrite H6 in H1.
Qed.

Lemma ltn_addn1 : forall n, n<n+1.
Proof. move=> n; rewrite addn1; apply: ltnSn. Qed.

Lemma iprod_rec : 
  forall n (f : ordinal (n + 1) -> R), iprod (setA (ordinal_finType (n + 1))) f =
    iprod (setA (ordinal_finType n)) (fun x => f ((@inj_ord n 1) x)) * (f (Ordinal (ltn_addn1 n))).
Proof.
move=> n f.
move: (@inj_dinj _ _ (setA (ordinal_finType n)) (@inj_ord n 1) (@inj_inj_ord n 1) ) => H1.
move: (@iprod_injection (ordinal_finType n) (ordinal_finType (n+1)) 
  (setA (ordinal_finType n)) (setA (ordinal_finType (n + 1))) (@inj_ord n 1) f H1) => H2; clear H1.
rewrite H2; congr mulR.
rewrite -iprod_set1.
apply: eq_iprod_set.
move=> x.
rewrite/ setD //.
rewrite (@inj_ord_image n 1 x) / setA andbT.
clear H2.
case: x =>//= x Hx.
symmetry.
case H1:(x<n) => //=; move/idP: H1 => H1.
  apply/eqP=> H2.
  move/ord_eqP: H2 => //=; move/eqP => H2.  
  rewrite H2 in H1.
  move: (ltnn x) => H4.
  by rewrite H1 in H4.
apply/eqP.
apply: ordinal_inj => //=.
move: (leqNgt n x) => H2.
move/negP: H1 => H1.
rewrite H1 in H2; clear H1.
move/idP: H2 => H2.
apply/eqP.
by rewrite eqn_leq H2 andTb -ltnS -(addn1 n).
Qed.

Lemma ltn_addn0 : forall n, 0<n+1.
Proof. move=> n; rewrite addn1; apply: ltn0Sn. Qed.

Lemma iprod_rec_inv : 
  forall n (f : ordinal (n + 1) -> R), iprod (setA (ordinal_finType (n + 1))) f =
     (f (Ordinal (ltn_addn0 n))) * iprod (setA (ordinal_finType n)) (fun x => f ((@inj_ord_add n 1) x)).
Proof.
move=> n f.
move: (@inj_dinj _ _ (setA (ordinal_finType n)) (@inj_ord_add n 1) (@inj_inj_ord_add n 1) ) => H1.
move: (@iprod_injection (ordinal_finType n) (ordinal_finType (n+1)) 
  (setA (ordinal_finType n)) (setA (ordinal_finType (n + 1))) (@inj_ord_add n 1) f H1) => H2; clear H1.
rewrite H2 mulC; congr mulR.
rewrite -iprod_set1.
apply: eq_iprod_set.
move=> x.
rewrite/ setD //.
rewrite (@inj_ord_add_image n 1 x) / setA andbT.
clear H2.
case: x =>//= x Hx.
symmetry.
case H1:(0<x) => //=; move/idP: H1 => H1.
  apply/eqP=> H2.
  move/ord_eqP: H2 => //=; move/eqP => H2.  
  rewrite H2 in H1.
  move: (ltnn x) => H4.
  by rewrite H1 in H4.
apply/eqP.
apply: ordinal_inj => //=.
move: (leqNgt x 0) => H2.
move/negP: H1 => H1.
rewrite H1 in H2; clear H1.
move/idP: H2 => H2.
apply/eqP.
by rewrite eq_sym -leqn0.
Qed.

End indexed_products.
