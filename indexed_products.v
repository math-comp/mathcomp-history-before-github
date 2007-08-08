Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp algebraic_struct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section IndexedOperation.

Open Scope monoid_scope.



(*
Notation "x * y" := (mulR x y).
Notation "1" := e.
Hypotheses
  (mulP : forall x1 x2 x3, x1 * (x2 * x3) = (x1 * x2) * x3)
  (mulC : forall x1 x2, x1 * x2 = x2 * x1)
  (unitP : forall x, 1 * x = x).
*)

Section iprod.

Variables (R : monoid) (d : finType) (a : set d) (f : d->R).

Notation mulR := (fun x y :R => x * y).

Definition iprod := foldr (fun x => mulR (f x)) 1 (filter a (enum d)).

End iprod.

Section monoid_iprod.
(* Lemma for non abelian monoid *)

Variable (R : monoid) (d : finType).
(* Notation mulR := (fun x y :R => x * y). *)

Lemma eq_iprod_set_: forall a b (f:d->R),
  a =1 b -> iprod a f = iprod b f.
Proof.
move => a b N H; rewrite /iprod; elim (enum d) => [| x s Hrec] //=.
by rewrite H; case (b x) => //=; congr (_ * _).
Qed.

Lemma eq_iprod_f_: forall (a:set d) (f g:d->R),
  dfequal a f g -> iprod a f = iprod a g.
Proof.
move => a f g H; rewrite /iprod.
elim: (enum d) => //=.
by move => x s IHs; case E: (a x) => //=; rewrite H => //; congr (_ * _).
Qed.

Lemma eq_iprod_ : forall a b (f g : d->R),
  a =1 b -> dfequal a f g -> iprod a f = iprod b g.
Proof.
move=> a b f g; move/eq_iprod_set_=> <-; exact: eq_iprod_f_.
Qed.

Lemma iprod_set0_eq_ : forall (f:d->R), iprod set0 f = 1.
Proof. by move => f; rewrite /iprod filter_set0. Qed.

Lemma iprod_set0_ : forall (r : set d) (f:d->R),
  r =1 set0 -> iprod r f = 1.
Proof. move=> r f; move/eq_iprod_set_->; exact: iprod_set0_eq_. Qed.

Lemma iprod_f1_eq_ : forall (a:set d), iprod a (fun x => 1) = 1 :> R.
Proof.
move => a; rewrite /iprod.
by elim: (filter a (enum d)) => //=; move => x s Hs; rewrite m_op_unitl.
Qed.

Lemma iprod_f1_ : forall (r : set d) (f:d->R),
  dfequal r f (fun _=> 1) -> iprod r f = 1.
Proof. move=> r f; move/eq_iprod_f_->; exact: iprod_f1_eq_. Qed.

Lemma iprod_set1_eq_ : forall (i0 : d) (f:d->R),
  iprod (set1 i0) f = f i0.
Proof.
move => i0 f; rewrite /iprod. 
move: (count_set1_uniq i0 (uniq_enum d)).
rewrite count_filter mem_enum /setA /nat_of_bool.
have H : filter (set1 i0) (enum d) i0 by rewrite filter_enum; apply/set1P.
move: H; case: (filter (set1 i0) (enum d)) => //=.
by move => x [|x' s'] //= ;
  rewrite /setU1 orbF => Heq; rewrite (eqP Heq) m_op_unitr.
Qed.

Lemma iprod_set1_ : forall i0 (r : set d) (f :d->R),
  r =1 set1 i0 -> iprod r f = f i0.
Proof. move=> i0 r F; move/eq_iprod_set_->; exact: iprod_set1_eq_. Qed.

Lemma iprod_eta_ : forall r (f : d->R), 
  iprod r f = (iprod (fun i : d => r i) (fun i : d => f i)).
Proof. move=> *; exact: eq_iprod_. Qed.

Lemma iprod_etaA : forall (f : d->R),
 iprod (setA d) f = (iprod (setA d) (fun i : d => f i)).
Proof. move=> *; exact: eq_iprod_. Qed.

End monoid_iprod.

Section ab_monoid_iprod.
Variable (R : ab_monoid).

Lemma iprodD1_ : forall (d : finType) x (a : set d) (f : d->R),
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
    rewrite -!(eqP H3) setD11; congr (_ * _); congr foldr. 
    apply: eqd_filter => x2 Hx2; rewrite /setD1 /setU1.
    case E2: (x1 == x2) => /=; first by case H1; rewrite (eqP E2).
    by rewrite mem_filter /setI Hx2 andbT.
  have F2: setD1 (setU1 x1 (filter a s1)) x x1.
    rewrite mem_filter in H3; case/andP: H3 => H3 H4.
    rewrite /setD1 /setU1 mem_filter /setI.
    case E2: (x==x1) => /=; first by case H1; rewrite -(eqP E2).
    by rewrite eq_refl.
  rewrite F2 Hrec //= !m_op_A //; congr (_ * _); first exact: m_op_C. 
  congr foldr; apply eqd_filter => x2 Hx2; rewrite /setD1 /setU1.
  case E2: (x==x2)=>//=; rewrite mem_filter /setI.
  case (a x2) => //=; case E3:(x1==x2) => //=;
    by case H1; rewrite (eqP E3).
move => H3; rewrite Hrec //; congr (_ * _); congr foldr.
have F2: setD1 (filter a s1) x x1 = false.
  by rewrite /setD1 mem_filter /setI E1 /= andbF.
by rewrite F2.
Qed.

Lemma iprod_setU_ : forall (d : finType) (a b: set d)(f:d->R),
 disjoint a b -> iprod (setU a b) f = iprod a f * iprod b f.
Proof.
move => d a b f.
elim: {a}(card a) {-2}a (refl_equal (card a)) b => [| n Hrec] a Ha b Hab.
  rewrite (eq_iprod_set_ _ (card0_eq Ha)) iprod_set0_eq_ m_op_unitl//.
  have F1: setU a b =1 b by move => x; rewrite /setU (card0_eq Ha).
  by rewrite (eq_iprod_set_ _  F1).
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ x) ?(@iprodD1_ _ x a) //; last by rewrite /setU Hx.
rewrite -m_op_A//; congr (_ * _).
have F0: card (setD1 a x) = n. 
  by apply (@addn_injl 1%N); rewrite (add1n n) -Ha (cardD1 x a) Hx.
have F1: setD1 (setU a b) x =1 setU (setD1 a x) b.
  move => x1; rewrite /setD1 /setU.
  case E1: (x == x1) => //=; rewrite /disjoint /set0b in Hab.
  move: (card0_eq (eqP Hab)) => H1. 
  case E2: (b x1) => //; case (H1 x1); by rewrite /setI E2 -(eqP E1) Hx.
rewrite (eq_iprod_set_ _ F1) Hrec // /disjoint; apply/set0P => x1.
rewrite /setI /setD1.
case E1: (x==x1) => //=. 
rewrite /disjoint /set0b in Hab; move: (card0_eq (eqP Hab)) => H1.
case E2: (a x1) => //=.
by move: (H1 x1); rewrite /setI E2.
Qed.

Lemma iprodID_ : forall (d : finType) (c r :set d) (f : d-> R),
  iprod r f = iprod (fun i : d => r i && c i) (fun i => f i) * 
              iprod (fun i => r i && ~~ c i) (fun i => f i).
Proof.
move=> d c r F; rewrite -iprod_setU_ /setU //.
  by apply: eq_iprod_set_ => i; case r; case c.
by apply/set0P=> i; rewrite /setI; case r; case c.
Qed.

Lemma iprod_mult_ : forall (d : finType) (a : set d)(f g : d->R),
  iprod a (fun x => f x * g x) = iprod a f * iprod a g.
Proof.
move => d a f g.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
  by rewrite !(eq_iprod_set_ _ (card0_eq Ha)) !iprod_set0_eq_ m_op_unitl.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite !(@iprodD1_ _ x a) // -(m_op_A (f x) (iprod (setD1 a x) f)). 
rewrite (m_op_A (iprod (setD1 a x) f)) (m_op_C (iprod (setD1 a x) f))
  -!m_op_A -Hrec //.
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.

Lemma iprod_dimage_ : forall (d : finType) (a : set d) (f:d->R) (g:d->d),
 disjoint a (image g a) -> dinjective a g ->
 iprod (setU a (image g a)) f = iprod a (fun x => f x * f (g x)).
Proof.
move => d a f g.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha Hd Hi.
  rewrite (eq_iprod_set_ _ (card0_eq Ha)) iprod_set0_eq_ 
    (@eq_iprod_set_ _ d (setU a (image g a)) set0 f);
    first exact: iprod_set0_eq_.
  move => x; rewrite /setU (card0_eq Ha) /=; apply/imageP.
  by move => [y Hay _]; rewrite (card0_eq Ha) in Hay.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ x); last by rewrite /setU; apply/orP;left.
rewrite (@iprodD1_ _ x a) //= -m_op_A; congr (_ * _).
rewrite (@iprodD1_ _ (g x)); first (congr (_ * _)).
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
        by apply/andP; split => //=; apply/imageP;
          exists w => //=; apply/eqP.
      have F1 : (g x != y).
        apply/negP => Hgx; move/eqP: Hgx => Hgx;
          case Hd; exists y; rewrite /setI.
        by apply/andP; split => //=; apply/imageP; exists x =>//=.
      by rewrite F1 orbF.
    rewrite andbF /=; apply/andP/imageP.
      move => [Hgxy H']; move/andP: H' => [Hxy Him];
        move/imageP: Him => [w Haw Hwy].
      exists w => //; apply/andP; split => //.
      by apply/negP => Hxw; case/negP: Hgxy; apply/eqP;
       rewrite Hwy; congr g; apply/eqP.
    move => [w H' Hwy]; move/andP: H' => [Hxw Haw]; split.
      rewrite Hwy; apply/negP => Hgxy; case/negP: Hxw.
      by apply/eqP; apply: Hi => //; apply/eqP.
    apply/andP;split.
      apply/negP;move => Hxy; apply Hd;exists y;
        rewrite /setI; apply/andP;split; first by rewrite -(eqP Hxy).
      by apply/imageP; exists w => //.
    by apply/imageP; exists w => //.
  rewrite (@eq_iprod_set_  _ _ _ _ _ F1) //; apply Hrec; first
    by (apply: (@addn_injl 1%N); 
          rewrite (add1n n) -Ha; rewrite (cardD1 x a) Hx => //=).
    apply/set0Pn; rewrite /setD1 /setI;
      move => [x0 H']; move/andP: H' => [Hdx Hidx].
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

Lemma partition_iprod_ : 
  forall (d d': finType) (pr : set d) p (r : set d') (f :d'->R),
    (forall j, r j -> pr (p j)) ->
      iprod r f =
        iprod pr (fun i => (iprod (fun j=> r j && (p j==i)) (fun j=> f j))).
Proof.
move=> d d' pr p r f prp.
rewrite (@eq_iprod_set_ _ _ _ (fun j => r j && pr (p j))); last first.
  by move=> i /=; case ri: (r i); rewrite // prp.
rewrite iprod_eta_; elim: {pr}_.+1 {-2}pr {prp} (ltnSn (card pr)) => // n IHn pr.
case: (pickP pr) => [i0 pri0 | pr0 _]; last first.
  by rewrite !iprod_set0_ => //= i; rewrite pr0 andbF.
rewrite ltnS (cardD1 i0) pri0 (@iprodD1_ _ i0) //; move/IHn=> {n IHn} <-.
rewrite (@iprodID_ _ (fun j => p j == i0));
  (congr (_ * _); apply: eq_iprod_set_) => [j | i].
- by case: eqP => [-> | _]; rewrite ?pri0 ?andbF ?andbT.
by rewrite /setD1 eq_sym -!andbA; do !bool_congr.
Qed.
Implicit Arguments partition_iprod_ [d d' r f].

End ab_monoid_iprod.

Section iprod_dist.

Variable (R : ab_monoid) (d : finType) (m' : R -> R -> R) (o : R->R).

Hypothesis distr : forall x y z, m' (x * y) z = (m' x z) * (m' y z).
Hypothesis distl : forall x y z, m' x (y * z) = (m' x y) * (m' x z).
Hypothesis m'1x : forall x, m' 1 x = 1.
Hypothesis m'x1 : forall x, m' x 1 = 1.
Hypothesis o1 : o 1 = 1.
Hypothesis disto : forall x y, o (x * y) = o x * o y.

Lemma i_prod_distr_ : forall (a:set d) alpha f,
  iprod a (fun x => m' (f x) alpha) = m' (iprod a f) alpha.
Proof.
move => a alpha f.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
 by rewrite !(eq_iprod_set_ _ (card0_eq Ha)) !iprod_set0_eq_ m'1x.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ _ x) //=; rewrite (@iprodD1_ _ _ x a) //=. 
rewrite distr; congr (_ * _); apply Hrec. 
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.

Lemma i_prod_distl_ : forall (a:set d) alpha f,
  iprod a (fun x => m' alpha (f x)) = m' alpha (iprod a f).
Proof.
move => a alpha f.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
  by rewrite !(eq_iprod_set_ _ (card0_eq Ha)) !iprod_set0_eq_ m'x1.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ _ x) //=; rewrite (@iprodD1_ _ _ x a) //=. 
rewrite distl; congr (_ * _); apply Hrec. 
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.

Lemma iprod_distf_ : forall (a : set d) (f :d->R),
  iprod a (fun i => o (f i)) = o (iprod a (fun i => f i)).
Proof.
move=> a f.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha.
  by rewrite !(eq_iprod_set_ _ (card0_eq Ha)) !iprod_set0_eq_ o1.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ _ x) //=; rewrite (@iprodD1_ _ _ x a) //=. 
rewrite disto; congr (_ * _); apply Hrec. 
by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
Qed.

End iprod_dist.

Section iprod_reindex.
Variable (R : ab_monoid).

Lemma reindex_iprod_onto_ : forall (d d' : finType) (h : d' -> d) h' r (f :d->R),
  dcancel r h' h -> 
    iprod r f = iprod (fun i => (h' (h i) == i) && r (h i)) (fun i=> f (h i)).
Proof.
move=> d d' h h' r f h'K.
elim: {r}_.+1 {-3}r h'K (ltnSn (card r)) => //= n IHn r h'K.
case: (pickP r) => [i ri | r0 _]; last first.
  by rewrite !iprod_set0_ // => x; rewrite r0 andbF.
rewrite ltnS (cardD1 i) ri add1n; move/IHn {n IHn} => IH.
rewrite (iprodD1_ f ri) (@iprodD1_ _ _ (h' i)) h'K ?set11 //; congr (_ * _).
rewrite {}IH => [|j]; [apply: eq_iprod_set_ => j | by case/andP; auto].
rewrite / setD1 (andbCA (~~ _)); case: eqP => //= hK; congr (~~ _ && _).
by apply/eqP/eqP=> [-> | <-] //; rewrite h'K.
Qed.
Implicit Arguments reindex_iprod_onto_ [d d' r f].

Lemma reindex_iprod_ : forall (d d' : finType) (h : d' -> d) r (f :d->R),
  ibijective r h ->
    iprod r f = iprod (fun i => r (h i)) (fun i=> f (h i)).
Proof.
move=> d d' h r F [h' hK h'K]; rewrite (reindex_iprod_onto_ h h' h'K).
by apply: eq_iprod_set_ => i; case Hi: (r _); rewrite ?andbF ?hK ?set11.
Qed.
Implicit Arguments reindex_iprod_ [d d' r f].

Lemma i_prod_image_ :
  forall (d:finType) (a:set d) (g:d->d) (f : d->R), dinjective a g ->
   iprod (image g a) f = iprod a (fun x => f (g x)).
Proof.
move => d a.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha g f Hg.
  have F1: a =1 set0 by apply card0_eq.
  have F2: image g a =1 set0. 
    by move => x; rewrite (@image_eq _ _ a set0 g g) //;
      rewrite (@image_set0 d d g x).
  by rewrite (@eq_iprod_set_ _ d _ _ _ F1) (@eq_iprod_set_ _ d _ _ _ F2)
    !iprod0_.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ _ x a) => //.
rewrite (@iprodD1_ _ _ (g x)); last by apply/imageP; exists x.
congr (_ * _).
have F3: setD1 (image g a) (g x) =1 image g (setD1 a x).
  move => y;apply/andP/imageP.
    move => [Hngx Hin]; move/imageP: Hin => [z Hin Heq];exists z =>//.
    apply/andP; split => //; apply/negP; move => Heq'. 
    by rewrite (eqP Heq') in Hngx; case/negP: Hngx; rewrite Heq.
  move => [z Hin Heq]; move/andP: Hin => [Hzx Hin]; split.
    apply/negP;move/eqP => Heq'.
    by move/negP: Hzx => H; case H; apply/eqP; apply Hg => //;
      rewrite -Heq.
  by apply/imageP; exists z.
rewrite (@eq_iprod_set_ _ d _ _ _ F3); apply Hrec => //.
  by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
move => x' y' Hx' Hy' Heq; move/andP:Hx'=>[_ Hx']; move/andP:Hy'=>[_ Hy']. 
by apply Hg => //.
Qed.

Lemma i_prod_image2_ :
  forall (d d':finType) (a:set d) (g:d->d') f, dinjective a g ->
   iprod (image g a) f = iprod a (fun x => f (g x)) :> R.
Proof.
move => d d' a.
elim: {a}(card a) {-2}a (refl_equal (card a)) => [| n Hrec] a Ha g f Hg.
  have F1: a =1 set0 by apply card0_eq.
  have F2: image g a =1 set0 
    by move => x; rewrite (@image_eq _ _ a set0 g g) //;
    rewrite (@image_set0 d d' g x).
  by rewrite (@eq_iprod_set_ _ d _ _ _ F1) (@eq_iprod_set_ _ d' _ _ _ F2)
    !iprod0_.
have F2: ~~set0b a by apply/set0P => H1; rewrite (eq_card0 H1) in Ha.
case/set0Pn: F2 => x Hx.
rewrite (@iprodD1_ _ _ x a) => //.
rewrite (@iprodD1_ _ _ (g x)); last by apply/imageP; exists x.
congr (_ * _).
have F3: setD1 (image g a) (g x) =1 image g (setD1 a x).
  move => y;apply/andP/imageP.
    move => [Hngx Hin]; move/imageP: Hin => [z Hin Heq];exists z =>//.
    apply/andP; split => //; apply/negP; move => Heq'. 
    by rewrite (eqP Heq') in Hngx; case/negP: Hngx; rewrite Heq.
  move => [z Hin Heq]; move/andP: Hin => [Hzx Hin]; split.
    apply/negP;move/eqP => Heq'.
    by move/negP: Hzx => H; case H; apply/eqP; apply Hg => //; rewrite -Heq.
  by apply/imageP; exists z.
rewrite (@eq_iprod_set_ _ d' _ _ _ F3); apply Hrec => //.
  by rewrite (cardD1 x) Hx /= add1n in Ha; injection Ha.
move => x' y' Hx' Hy' Heq; move/andP:Hx'=>[_ Hx']; move/andP:Hy'=>[_ Hy']. 
by apply Hg => //.
Qed.

Lemma iprod_injection_ : 
  forall (d d':finType) (a:set d) (a' :set d') (f:d->d') g,
    dinjective a f ->
      iprod a' g =
      iprod (setI a (preimage f a')) (fun x => g (f x)) *
      iprod (setD a' (image f a)) g :> R.
Proof.
move => d d' a a' f g Hinj.
have Hinj' : dinjective (setI a (preimage f a')) f.
  by move => x y Hx Hy; case/andP: Hx => Hx _; case/andP: Hy => Hy _;
    apply:Hinj.
rewrite -(@i_prod_image2_ d d' (setI a (preimage f a')) f g) // -iprod_setU_.
  apply: eq_iprod_set_; move => x; rewrite /setU /setD.
  case A: (image f a x)=>//=; first (rewrite orbF; case/imageP: A => y B C).
    apply/idP/imageP; first by move=>D; exists y=>//; 
      rewrite /setI B /preimage -C.
    by case => x' Hx' Hf'; case/andP: Hx' => _ Ha'; rewrite Hf'.
  case H': (a' x); first (by rewrite orbT).
  rewrite orbF; apply/idP/imageP; first done.
  by case => y Hy Hf; move/andP: Hy => [Ha Ha']; rewrite -H' Hf.
apply: (@disjoint_trans d' _ (image f a)); rewrite /setI/setD.
  rewrite /subset disjoint_subset;apply/subsetP=>x A.
  case/imageP:A =>y B C; rewrite /setC negb_involutive.
  by case/andP: B=>B _; apply/imageP; exists y.
by apply/set0P; rewrite /setI //=; move =>x //=; case: (image f a x) => //.
Qed.

End iprod_reindex.

(*
Lemma ltn_addr : forall m n p, m < n -> m < n + p.
Proof.
move=> m n p H.
rewrite -(ltn_add2r p _ _ ) in H.
apply: (@leq_trans (m + p).+1 _ _)=>//.
apply: leq_addr.
Qed.

Lemma ltn_addl : forall m n p, m < n -> m < p + n.
Proof.
move=> m n p H.
rewrite -(ltn_add2l p _ _ ) in H.
apply: (@leq_trans (p + m).+1 _ _)=>//.
apply: leq_addl.
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
*)


End IndexedOperation.
