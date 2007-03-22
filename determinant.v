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
  (distrR : forall x1 x2 x3, mult (plus x1 x2) x3=plus (mult x1 x3)(mult x2 x3))
  (plus_m_one : plus one m_one = zero).

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

Lemma determinant_multilinear :
 forall (range:set d) (a b c:d->d->R) i (beta gamma:R),
  range i ->
  (forall k, setD1 range i k -> forall j, range j -> b k j = a k j /\ c k j = a k j) ->
  (forall j, range j -> a i j = plus (mult beta (b i j))(mult gamma (c i j))) ->
 determinant range a = plus (mult beta (determinant range b))
    (mult gamma (determinant range c)).
move => range a b c i beta gamma Hi; rewrite /determinant.
have: forall x y, perm range x -> range (x y) = range y by exact: perm_closed.
have F' : forall x, perm range x -> perm range x by done.
elim: (card (perm range)) {-2 4}(perm range)(conj (refl_equal (card (perm range))) F'). 
move => perm [Hperm Hperm'] Hclosed Hs Hl.
 rewrite !(eq_iprod_set _ _ _ _ _ _ _ (card0_eq Hperm)) !iprod0 -!(multC zero).
 by rewrite !mult0x plus0x.
move => n Hrec perm_set [Hperm Hperm'] Hclosed Hs Hl.
have F2: ~~set0b perm_set by apply/set0P => H1; rewrite (eq_card0 H1) in Hperm.
case/set0Pn: F2 => sigma Hsigma.
rewrite !(iprodD1 _ plus zero _ _ _ sigma perm_set) //.
rewrite (multC beta)(multC gamma) !distrR -!(multC beta) -!(multC gamma).
have F: forall x1 x2 x3 x4, plus (plus x1 x2) (plus x3 x4) = 
          plus (plus x1 x3) (plus x2 x4).
 by move => x1 x2 x3 x4; rewrite -!plusA; congr plus; rewrite !plusA (plusC x3). 
have F1 : card (setD1 perm_set sigma) = n.
 by rewrite (cardD1 sigma) /nat_of_bool Hsigma // in Hperm; injection Hperm.
have F2 : forall x, setD1 perm_set sigma x -> perm range x.
 by move => x H; move/andP: H => [_ H]; apply Hperm'.
have F3 : forall x y, setD1 perm_set sigma x -> range (x y) = range y.
 by move => x y H; move/andP: H => [_ H]; apply Hclosed.
rewrite F; rewrite Hrec //.
rewrite (prod_multilinear _ a b c i _ _ Hi Hs Hl) //.
rewrite (multC (b2R (perm_signature d sigma))) distrR.
rewrite -!(multC (b2R (perm_signature d sigma))) !multA. 
rewrite -!(multC (b2R (perm_signature d sigma))).
congr plus.
by apply Hperm'.
Qed.

Definition pos_perm (d:finType)(r:set d) :=
   setI (perm r) (fun s => ~~perm_signature d s).

Definition cb_transpose (d:finType)(i j:d)(s:permType d) :=
  perm_mul (transperm i j) s.

Lemma perm_transpose : forall (r:set d) i j, r i -> r j ->
  perm r (transperm i j).
move => r i j Hi Hj; apply/subsetP=> x.
rewrite /= /transperm p2f /transpose.
case E1: (i == x); first by rewrite -(eqP E1).
case E2: (j == x); first by rewrite -(eqP E2).
by move/negP=> H; case H.
Qed.

Lemma perm_compose : 
 forall r s1 s2, perm r s1 -> perm r s2 -> 
 perm r (perm_mul (d:=d) s1 s2).
move => r s1 s2 H1 H2; apply/subsetP => x Hx.
case E1: (s1 x == x).
 rewrite /perm_mul p2f /comp in Hx; rewrite (eqP E1) in Hx.
 by move/subsetP: H2 => H2; apply H2.
by move/subsetP: H1 => H1; apply: H1; rewrite E1.
Qed.


Lemma can_cb_transpose :
 forall i j, cancel (cb_transpose d i j) (cb_transpose d i j).
move => i j sigma; rewrite /cb_transpose perm_mulP.
move: square_transperm => st; rewrite /mulg/= in st; rewrite st.
 by rewrite perm_unitP.
Qed.

Lemma perm_partition_transpose :
  forall (r:set d) i j, i != j -> r i -> r j ->
     setU (pos_perm d r)(image (cb_transpose d i j) (pos_perm d r)) =1 perm r.
move => r i j Hdiff Hi Hj sigma. 
have F1: forall s, pos_perm d r s -> perm r s by move => s; move/andP => [H _].
have F0: forall s, pos_perm d r s -> perm r (cb_transpose d i j s).
 move => s Hs; rewrite /cb_transpose. 
 apply: perm_compose; first by apply: perm_transpose => //. 
 by apply F1.
have F2: (cb_transpose d i j (cb_transpose d i j sigma)) = sigma.
  by apply: can_cb_transpose.
apply/idP/idP => Hsigma.
 move/orP: Hsigma => Hsigma; case: Hsigma => Hsigma; first by apply F1.
 by move/imageP: Hsigma => [y Hry Heq]; rewrite Heq; apply F0.
apply/orP => /= ; case E1: (perm_signature d sigma);
 last by left; apply/andP; split => //; rewrite E1.
right;apply/imageP; exists (cb_transpose d i j sigma) => //.
rewrite /cb_transpose; apply/andP; split.
 by apply perm_compose => //; apply perm_transpose.
by rewrite perm_signatureM signature_transperm Hdiff E1.
Qed.

Lemma disjoint_image : forall a i j, i != j -> 
  disjoint (setI a (fun s => ~~perm_signature d s))
   (image (cb_transpose d i j) (setI a (fun s => ~~ perm_signature d s))).
move => a i j Hdiff; apply/set0P => x; rewrite /setI.
case E1: (perm_signature d x); first by rewrite andbF.
case E2: (a x) => //=.
have F:~(image (cb_transpose d i j)(setI a (fun s => ~~perm_signature d s)) x).
 move/imageP=>[y Hin Heq]; rewrite Heq /cb_transpose perm_signatureM in E1.
 move/andP: Hin => [_ Hin]; case E3: (perm_signature d y); rewrite E3 in Hin => //.
 by rewrite E3 signature_transperm Hdiff in E1 => //.
case E: (image (cb_transpose d i j) (fun s => a s && ~~perm_signature d s) x)=> //.
Qed.

Lemma alternate_determinant :
 forall (range:set d) i j a, range i -> range j -> i != j ->
   (forall k, range k -> a i k = a j k) ->
   determinant range a = zero.
move => r i j a Hi Hj Hdiff Hcol; rewrite /determinant.
have F1: (perm r =1 setU (pos_perm d r) (image (cb_transpose d i j) (pos_perm d r))).
 by move => x; rewrite perm_partition_transpose.
rewrite {F1} (eq_iprod_set _ _ _ _ _ _ _ F1).
have F2: disjoint (pos_perm d r) (image (cb_transpose d i j)(pos_perm d r))
  by apply: disjoint_image.
have F3: (dinjective (pos_perm d r) (cb_transpose d i j)).
 by apply inj_dinj; apply: can_inj (can_cb_transpose i j).
rewrite iprod_parts => //.
have F4: forall sigma, pos_perm d r sigma ->
            iprod R mult one d r (fun k => a k (cb_transpose d i j sigma k))=
                          iprod R mult one d r (fun k => a k (sigma k)).
 move => sigma Hsigma; rewrite (iprodD1 _ _ _ _ _ _ i) => //. 
 rewrite (iprodD1 R _ _ _ _ _ j (setD1 r i)) => //; last by apply/andP.
 rewrite (iprodD1 R _ _ _ _ _ i r) => //.
 rewrite (iprodD1 R _ _ _ _ _ j (setD1 r i)) => //; last by apply/andP.
 rewrite !multA.
 rewrite /cb_transpose /perm_mul !p2f /comp /transperm !p2f /transpose.
 case E1: (i==i); last by (move/eqP: E1).
 case E2: (i==j); first by move/eqP: Hdiff;rewrite (eqP E2).
 case E3: (j==j); last by (move/eqP: E3).
 have F5: (mult (a i (sigma j))(a j (sigma i)))= 
          (mult (a i (sigma i))(a j (sigma j))).
  have F6: r (sigma j) by move/andP: Hsigma => [Hsigma _]; rewrite perm_closed.
  have F7: r (sigma i) by move/andP: Hsigma => [Hsigma _]; rewrite perm_closed.
  by rewrite !Hcol.
 rewrite F5; congr mult; apply eq_iprod_f => x Hx; rewrite !p2f.
 move/andP: Hx => [Hjx Hx]; move/andP: Hx => [Hix Hx].
 case E4: (i==x); first by move/eqP: Hix; rewrite (eqP E4).
 case E5: (j==x) => //; by move/eqP: Hjx; rewrite (eqP E5).
 have F6: forall sigma, pos_perm d r sigma -> plus
        (mult (b2R (perm_signature d sigma))
           (iprod R mult one d r (fun i0 : d => a i0 (sigma i0))))
        (mult (b2R (perm_signature d (cb_transpose d i j sigma)))
           (iprod R mult one d r
              (fun i0 : d => a i0 (cb_transpose d i j sigma i0)))) = zero.
 move => sigma Hsigma; rewrite F4 => //; rewrite -distrR.
 rewrite /cb_transpose perm_signatureM signature_transperm Hdiff.
 have F7: plus (b2R (perm_signature d sigma))(b2R (true (+) perm_signature d sigma))=
          zero   by case: (perm_signature d sigma) => //=; rewrite plusC.
 by rewrite F7.
 rewrite (eq_iprod_f R _ _ _ _ _ (fun x => zero)); last by exact: F6.
by apply iprod_1.
Qed.

End R_props.
End determinant_context.
