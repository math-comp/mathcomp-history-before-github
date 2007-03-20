Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp signperm indexed_products.

Section determinant_context.
Variables (d:finType)(R:Type)(plus mult : R -> R -> R)(zero one m_one : R).

Definition b2R (b:bool) := if b then m_one else one.

Definition determinant (range:set d)(a:d->d->R) : R :=
  iprod R plus zero (perm_finType d)(perm range)
  (fun sigma => (mult (b2R (perm_signature d sigma)))
       (iprod R mult one d range (fun i => a i (fun_of_perm sigma i)))).

Section R_props.
Hypotheses (mult1x : forall x, mult one x = x)
  (mult0x : forall x, mult zero x = zero)
  (plus0x : forall x, plus zero x = x)
  (plusA : forall x1 x2 x3, plus x1 (plus x2 x3) = plus (plus x1 x2) x3)
  (plusC : forall x1 x2, plus x1 x2=plus x2 x1)
  (multA : forall x1 x2 x3, mult x1 (mult x2 x3) = mult (mult x1 x2) x3)
  (multC : forall x1 x2, mult x1 x2 = mult x2 x1)
  (distrR : forall x1 x2 x3, mult (plus x1 x2) x3=plus (mult x1 x3)(mult x2 x3)).

Lemma prod_multilinear :
 forall (range:set d) (a b c:d->d->R) i (beta gamma:R),
  range i ->
  (forall k, setD1 range i k -> forall j, range j -> b k j = a k j /\ c k j = a k j) ->
  (forall j, range j -> a i j = plus (mult beta (b i j))(mult gamma (c i j))) ->
  forall sigma, perm range sigma ->
    iprod R mult one d range (fun i => a i (fun_of_perm sigma i)) =
    plus 
     (mult beta (iprod R mult one d range (fun i => b i (fun_of_perm sigma i))))
     (mult gamma (iprod R mult one d range (fun i => c i (fun_of_perm sigma i)))).
move => range a b c i beta gamma Hr Hs Hc sigma Hp.
have H2: range =1  setU (set1 i) (setD1 range i).
move => x; apply/idP/idP.
intros H; case H': (i==x); rewrite /setU /setD1; rewrite H'.
 by apply/orP;left.
by rewrite H.
move => Hor; case/orP: Hor.
 by move => Hx; rewrite -(eqP Hx).
by move => Hand; case/andP: Hand.
have F1: disjoint (set1 i)(setD1 range i).
apply/set0Pn => x; move: x => [x H]; move/andP: H => [Hi Hd]; move/andP: Hd => [Hni _].
by move/negP: Hni.
have F2 : range (sigma i) by rewrite perm_closed.
rewrite !(eq_iprod_set _ _ _ _ _ _ _ H2) !iprod_setU ?iprod_set1 ?Hc => //.
have F3 : forall k, setD1 range i k -> b k (sigma k) = a k (sigma k).
 move => k H.
 have F4: range k by move/andP: H => [_ H].
 have F5: range (sigma k) by rewrite perm_closed.
 by case (Hs _ H _ F5).
rewrite (eq_iprod_f _ _ _ _ _ _ _ F3).
have F4 : forall k, setD1 range i k -> c k (sigma k) = a k (sigma k).
 move => k H.
 have F4: range k by move/andP: H => [_ H].
 have F5: range (sigma k) by rewrite perm_closed.
 by case (Hs _ H _ F5).
rewrite (eq_iprod_f _ _ _ _ _ _ _ F4).
by rewrite !multA distrR.
Qed.

Check prod_multilinear.
Lemma determinant_multilinear :
 forall (range:set d) (a b c:d->d->R) i (beta gamma:R),
  range i ->
  (forall k, range k -> ~i==k -> forall j, b k j = a k j /\ c k j = a k j) ->
  (forall j, range j -> a i j = plus (mult beta (b i j))(mult gamma (c i j))) ->
 determinant range a = plus (mult beta (determinant range b))
    (mult gamma (determinant range c)).