Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype.
Require Import tuple paths connect div .
Require Import groups group_perm zp algebraic_struct.

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

Lemma iprod_etaA_ : forall (f : d->R),
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
        iprod pr (fun i => 
                      (iprod (fun j=> r j && (p j==i)) (fun j=> f j))).
Proof.
move=> d d' pr p r f prp.
rewrite (@eq_iprod_set_ _ _ _ (fun j => r j && pr (p j))); last first.
  by move=> i /=; case ri: (r i); rewrite // prp.
rewrite iprod_eta_; 
  elim: {pr}_.+1 {-2}pr {prp} (ltnSn (card pr)) => // n IHn pr.
case: (pickP pr) => [i0 pri0 | pr0 _]; last first.
  by rewrite !iprod_set0_ => //= i; rewrite pr0 andbF.
rewrite ltnS (cardD1 i0) pri0 (@iprodD1_ _ i0) //; move/IHn=> {n IHn} <-.
rewrite (@iprodID_ _ (fun j => p j == i0));
  (congr (_ * _); apply: eq_iprod_set_) => [j | i].
- by case: eqP => [-> | _]; rewrite ?pri0 ?andbF ?andbT.
by rewrite /setD1 eq_sym -!andbA; do !bool_congr.
Qed.

End ab_monoid_iprod.
Implicit Arguments partition_iprod_ [R d d' r f].

Section iprod_reindex.
Variable (R : ab_monoid).

Lemma reindex_iprod_onto_ : 
  forall (d d' : finType) (h : d' -> d) h' r (f :d->R),
    dcancel r h' h -> 
      iprod r f = 
      iprod (fun i => (h' (h i) == i) && r (h i)) (fun i=> f (h i)).
Proof.
move=> d d' h h' r f h'K.
elim: {r}_.+1 {-3}r h'K (ltnSn (card r)) => //= n IHn r h'K.
case: (pickP r) => [i ri | r0 _]; last first.
  by rewrite !iprod_set0_ // => x; rewrite r0 andbF.
rewrite ltnS (cardD1 i) ri add1n; move/IHn {n IHn} => IH.
rewrite (iprodD1_ f ri) (@iprodD1_ _ _ (h' i)) h'K ?set11 //;
 congr (_ * _).
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

Lemma pair_iprod_dep_ : forall (d d': finType) r r' (f : d -> d' -> R),
  iprod r (fun i => iprod (r' i) (f i)) = 
    iprod (fun u => r (fst u) && r' (fst u) (snd u)) 
      (fun u => f (fst u) (snd u)).
Proof.
move=> d d' r r' f; set p1 := @fst d d'; set p2 := @snd d d'.
rewrite (partition_iprod_ r p1) => [|j]; last by case/andP.
apply: eq_iprod_f_ => i ri.
rewrite (reindex_iprod_onto_ (pair i) p2) => [|[i' j]] /=.
  by rewrite iprod_eta_; apply: eq_iprod_set_ => j;
    rewrite !set11 ri andbT.
by case/andP=> _; move/eqP->.
Qed.

Lemma pair_iprod_ : forall (d d': finType) r r' (f : d -> d' -> R),
  iprod r (fun i => iprod r' (f i)) = 
  iprod (fun u => r (fst u) && r' (snd u)) 
      (fun u => f (fst u) (snd u)).
Proof. move=> *; exact: pair_iprod_dep_. Qed.

Lemma pair_iprodA_ : forall (d d': finType) (f : d -> d' -> R),
  iprod (setA _) (fun i => iprod (setA _) (f i)) = 
    iprod (setA _) (fun u => f (fst u) (snd u)).
Proof. move=> *; exact: pair_iprod_. Qed.

Lemma exchange_iprod_dep_ :
  forall (d d' : finType) (r : set d) (r' : d -> set d') (xr : set d') f,
    (forall i j, r i -> r' i j -> xr j) ->
      iprod r (fun i => iprod (r' i) (f i)) = 
      iprod xr (fun j => 
                iprod (fun i => r i && r' i j) (fun i=> (f i j))) :>R.
Proof.
move=> d d' r r' xr F rxr; rewrite !pair_iprod_dep_.
pose p u := let: (i, j) := u in (j, i).
rewrite (reindex_iprod_onto_ (p _ _) (p _ _)) => [|[//]].
apply: eq_iprod_ => [] [j i] //=; symmetry; rewrite set11 andbC.
case: (@andP (r i)) => //=; case; exact: rxr.
Qed.
Implicit Arguments exchange_iprod_dep_ [d d' r r' f].

Lemma exchange_iprod_ : forall (d d': finType) r r' (f : d -> d' -> R),
  iprod r (fun i=> iprod r' (f i)) = 
  iprod r' (fun j=> iprod r (fun i => f i j)).
Proof.
move=> d d' r r' F; rewrite (exchange_iprod_dep_ r') //;
  apply: eq_iprod_f_ => i Hi.
by apply: eq_iprod_set_ => j; rewrite Hi andbT.
Qed.

Lemma iprod_image_ :
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
    !iprod_set0_eq_.
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

Lemma iprod_image2_ :
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
    !iprod_set0_eq_.
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
rewrite -(@iprod_image2_ d d' (setI a (preimage f a')) f g) // -iprod_setU_.
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

Section iprod_ordinal.

Variable (R : ab_monoid).

Lemma iprod_ord_rec_r : forall n (f : I_(n.+1) -> R),
   iprod (setA I_(n.+1)) f =
   iprod (setA I_(n)) (fun x => f (lshiftSn x)) * (f (Ordinal (ltnSn n))).
Proof.
move=> n f.
rewrite (iprodID_ (fun i :I_(n.+1) => i <n) (setA I_(n.+1)) f).
congr (_ * _); last first.
  apply: iprod_set1_ => //= i; rewrite -leqNgt.
  case H:(n<=i);symmetry; apply/eqP.
    move/idP: H => H; case: i H => //= i i0 H.
    suffices: (n = i).
      move=> ni; move: i0; rewrite -ni => i0.
      by congr Ordinal; apply: bool_irrelevance.
    by apply/eqP; rewrite eqn_leq H -ltnS.
  rewrite leqNgt in H; move/negbEF: H => H He.
  suffices: (n=i); first (by move=> ni; clear He; rewrite -ni ltnn in H).
  clear H; case: i He=> //= i i0 He; by case: He.
set r:= (fun i : I_(n.+1) => setA I_(n.+1) i && (i < n)).
suffices: ((setA I_(n)) =1 (fun i => r (lshiftSn i))).
  move=> H; rewrite (eq_iprod_set_ _ H).
  rewrite -(iprod_image2_ (g:=(@lshiftSn n)) f);
    last (move=> x y _ _; case=>//=; apply: ordinal_inj).
  apply: eq_iprod_; last (by move=> i _ //).
  move=> i; case Hr:(r i); symmetry; apply/imageP.
    have Hi: i < n by rewrite / r //= in Hr.
    clear Hr; exists (Ordinal Hi) => //=.
    case: i Hi => i i0 Hi //=; rewrite / lshiftSn //=; congr Ordinal.
    by apply: bool_irrelevance.
  by move=> Hf; elim: Hf=> x Hx Hxi; rewrite -Hxi in Hx; rewrite Hx in Hr.
move=> i; rewrite / setA; symmetry; apply/eqP.
by case: i =>//= i Hi; apply/eqP; rewrite eqn_sub0.
Qed.

Lemma iprod_ord_rec_l : forall n (f : I_(n.+1) -> R),
  iprod (setA I_(n.+1)) f = 
  f (Ordinal (ltn0Sn n)) * iprod (setA I_(n)) (fun x => f (rshiftSn x)).
Proof.
move=> n f.
rewrite (iprodID_ (fun i :I_(n.+1) => 0==i) (setA I_(n.+1)) f).
congr (_ * _).
apply: iprod_set1_ => //= i.
(* when write (i != 0) the coercio form ordinal to nat don't work !!*)
set r:= (fun i : I_(n.+1) => setA I_(n.+1) i && (0 != i)).
suffices: ((setA I_(n)) =1 (fun i => r (rshiftSn i))).
  move=> H; rewrite (eq_iprod_set_ _ H).
  rewrite -(iprod_image2_ (g:=(@rshiftSn n)) f);
    last (move=> x y _ _; case=>//=; apply: ordinal_inj).
  apply: eq_iprod_; last (by move=> i _ //).
  move=> i; case Hr:(r i); symmetry; apply/imageP.
    have Hi: i.-1 < n.
      rewrite / r //= in Hr; move/idP: Hr => Hr; rewrite eq_sym -lt0n in Hr.
      apply: (@leq_trans i); last (case: i Hr=> //=).
      by rewrite -(@ltnSpred i 0)//.
    exists (Ordinal Hi) =>//=.
    case: i Hi Hr => //= i i0 Hi Hr; rewrite / rshiftSn. 
    apply: ordinal_inj => //=; rewrite / r //= in Hr.
    by symmetry; apply: (@ltnSpred i 0); rewrite ltn_neqAle leq0n andbT.
  by move=> Hf; elim: Hf=> x Hx Hxi; rewrite -Hxi in Hx; rewrite Hx in Hr.
by move=> i; rewrite / setA; symmetry; apply/eqP; case: i.
Qed.

End iprod_ordinal.

End IndexedOperation.

Unset Implicit Arguments.
