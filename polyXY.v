Require Import ssreflect ssrfun ssrbool choice eqtype ssrnat seq div fintype.
Require Import tuple finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
Require Import poly polydiv mxpoly binomial.
Local Open Scope ring_scope.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section extra_nat.

Lemma gtn_eqF (m n : nat) : m < n -> n == m = false.
Proof. by case: ltngtP. Qed.

End extra_nat.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Notation "'Y" := 'X%:P.

Notation "p .[ x , y ]" := (p.[x%:P].[y])
  (at level 2, left associativity, format "p .[ x ,  y ]") : ring_scope.

Section poly_extra.

Lemma polyX_eq0 (R : ringType) : 'X == 0 :> {poly R} = false.
Proof. by rewrite -lead_coef_eq0 lead_coefX oner_eq0. Qed.

Lemma size_map_poly_id0 (aR : ringType) (R : ringType) (f : {rmorphism aR -> R})
  (p : {poly aR}) (fp : f (lead_coef p) != 0) : size (p ^ f) = size p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite rmorph0 !size_poly0.
by rewrite size_poly_eq // fp lead_coef_eq0.
Qed.

Lemma map_poly_eq0_id0 (R R': ringType) (f : {rmorphism R -> R'})
  (p : {poly R}) : f (lead_coef p) != 0 -> (p ^ f == 0) = (p == 0).
Proof. by move=> lp_neq0; rewrite -!size_poly_eq0 size_map_poly_id0. Qed.

Lemma size_map_polyC (R : ringType) (p : {poly R}) :
  size (p ^ polyC) = size p.
Proof.
have [->|p_neq0] := altP (p =P 0); first by rewrite rmorph0 !size_poly0.
by rewrite size_map_poly_id0 // ?polyC_eq0 ?lead_coef_eq0.
Qed.

Lemma map_polyC_eq0 (R : ringType) (p : {poly R}) :
  (p ^ polyC == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_map_polyC. Qed.

Lemma map_resultant (F1 F2 : ringType) (p q : {poly {poly F1}})
  (f : {rmorphism {poly F1} -> F2}):
  f (lead_coef p) != 0 -> f (lead_coef q) != 0 ->
  f (resultant p q)= resultant (p ^ f) (q ^ f).
Proof.
move=> hp hq; rewrite /resultant /Sylvester_mx /=.
rewrite  -det_map_mx /= map_col_mx.
rewrite (@map_lin1_mx _ _ _ _ _ _ (poly_rV \o map_poly f p \o* rVpoly));
  last by move=> v; rewrite ?map_poly_rV /= -?map_rVpoly /= -rmorphM /=.
rewrite (@map_lin1_mx _ _ _ _ _ _ (poly_rV \o map_poly f q \o* rVpoly));
  last by move=> v; rewrite ?map_poly_rV /= -?map_rVpoly /= -rmorphM /=.
by rewrite !size_map_poly_id0.
Qed.


Lemma size_aXaddr (R : ringType) (a b : R) :
  a != 0 -> size (a *: 'X + b%:P) = 2.
Proof.
move=> a_neq0.
by rewrite -mul_polyC size_amulX polyC_eq0 size_polyC (negPf a_neq0).
Qed.

Lemma size_mulXr (R : comRingType) (a : R) : a != 0 -> size ('X * a%:P) = 2.
Proof. by move=> a0; rewrite mulrC mul_polyC -[_ *: _]addr0 size_aXaddr. Qed.

Lemma size_addXr (R : ringType) (b : R) : size ('X + b%:P) = 2.
Proof. by rewrite -['X]scale1r size_aXaddr ?oner_eq0. Qed.

Lemma size_subrX (R : ringType) (b : R) : size (b%:P - 'X ) = 2.
Proof. by rewrite -oppr_sub size_opp size_factor. Qed.

Lemma size_addNXr (R : ringType) (b : R) : size (- 'X + b%:P) = 2.
Proof. by rewrite addrC size_subrX. Qed.

Lemma size_comp_poly2 (R : idomainType) (p q : {poly R}) :
  size q = 2 -> size (p \Po q) = size p.
Proof.
move=> sq_eq2; have [] := ltngtP (size p) 1%N.
+ by rewrite ltnS leqn0 size_poly_eq0=> /eqP->; rewrite poly_com0p.
+ move=> sp_gt1; have : (size (p \Po q)).-1 = (size p).-1.
    by rewrite size_comp_poly_id sq_eq2 muln1.
  by rewrite -(subnKC sp_gt1) /=; case: size=> //= n ->.
+ by move=> /eqP /size1P [c c_neq0 ->]; rewrite poly_comCp.
Qed.

Lemma comp_poly2_eq0 (R : idomainType) (p q : {poly R}) :
  size q = 2 -> (p \Po q == 0) = (p == 0).
Proof. by move=> sq_eq2; rewrite -!size_poly_eq0 size_comp_poly2. Qed.

End poly_extra.

Section poly_eval_theory.

Definition eval (R : ringType) (x : R) := horner^~ x.

Variable R : comRingType.

Lemma eval_is_additive (x : R) : additive (eval x).
Proof. by rewrite /eval=> /= u v; rewrite horner_add horner_opp. Qed.

Canonical eval_additive (x : R) := Additive (eval_is_additive x).

Lemma eval_is_multiplicative (x : R) : multiplicative (eval x).
Proof. by rewrite /eval; split=> /=[u v|]; rewrite (horner_mul, hornerC). Qed.

Canonical eval_rmorphism (x : R) := AddRMorphism (eval_is_multiplicative x).

End poly_eval_theory.

Section swapXY.

Definition swapXY (R : ringType) (p : {poly {poly R}}) : {poly {poly R}} :=
  ((locked p) ^ (map_poly polyC)).['Y].
Implicit Arguments swapXY [[R]].

Lemma swapXY_is_additive (R : ringType) : additive (@swapXY R).
Proof. by move => p q; unlock swapXY; rewrite rmorph_sub !horner_lin. Qed.
Canonical swapXY_addf R := Additive (@swapXY_is_additive R).

Lemma swapXY_is_multiplicative (R : comRingType) : multiplicative (@swapXY R).
Proof.
by split=> [p q|]; unlock swapXY; rewrite (rmorph1, rmorphM) !horner_lin.
Qed.
Canonical swapXY_rmorph R := AddRMorphism (@swapXY_is_multiplicative R).

Lemma coef_swapXY (R : comRingType) (p : {poly {poly R}}) i j :
  (swapXY p)`_i`_j = p`_j`_i.
Proof.
unlock swapXY; rewrite horner_coef !coef_sum; set n := size _.
symmetry; transitivity (\sum_(k < n | k == j :> nat) p`_k`_i).
  have [lt_jn|gt_jn] := ltnP j n; first by rewrite (big_pred1 (Ordinal lt_jn)).
  suff pj_eq0 : p`_j = 0 by rewrite big1=> [|k /eqP ->]; rewrite pj_eq0 coef0.
  have [->|p_neq0] := eqVneq p 0; first by rewrite coefC if_same.
  have:= (leq_sizeP _ _ (leqnn n) _ gt_jn); rewrite coef_map /=; move/eqP.
  by rewrite map_polyC_eq0; move/eqP.
rewrite big_mkcond /=; apply: eq_bigr => k _.
rewrite coefM coef_sum big_ord_recr -polyC_exp big1; last first.
  by move => l _; rewrite coefC subn_eq0 leqNgt /= ltn_ord mulr0 coef0.
rewrite /= add0r subnn coefC eqxx 2!coef_map mul_polyC coefZ coefXn mulrC.
by rewrite eq_sym; case: ifP; rewrite (mul1r, mul0r).
Qed.

Lemma swapXYK (R : comRingType) : involutive (@swapXY R).
Proof. by move => p; do 2![apply/polyP=> ?]; rewrite !coef_swapXY. Qed.

Lemma swapXY_X (R : ringType) : swapXY 'X = 'Y :> {poly {poly R}}.
Proof. by unlock swapXY; rewrite map_polyX hornerX. Qed.

Lemma swapXY_polyC (R : ringType) (p : {poly R}) : swapXY p%:P = p ^ polyC.
Proof. by unlock swapXY; rewrite map_polyC /= hornerC. Qed.

Lemma swapXY_map_polyC (R : comRingType) (p : {poly R}) :
  swapXY (p ^ polyC) = p%:P.
Proof. by rewrite -swapXY_polyC swapXYK. Qed.

Lemma swapXY_eq0 (R : comRingType) (p : {poly {poly R}}) :
  (swapXY p == 0) = (p == 0).
Proof.
apply/idP/idP; first rewrite -{2}[p]swapXYK;
by move/eqP ->; unlock swapXY; rewrite map_polyC /= hornerC map_polyC.
Qed.

Definition sizeY (R : ringType) (p : {poly {poly R}}) : nat :=
  \max_(i < size p) (size (locked p)`_i).

(* more general version of sizeY *)
Lemma sizeYE (R : ringType) (p : {poly {poly R}}) :
  sizeY p = size (swapXY p).
Proof.
have [->|p_neq0] := eqVneq p 0.
  by rewrite swapXY_polyC rmorph0 /sizeY size_poly0 big_ord0.
unlock swapXY sizeY; rewrite horner_coef /=.
rewrite size_map_poly_id0 ?map_polyC_eq0 ?lead_coef_eq0 //.
apply/eqP; rewrite eqn_leq (leq_trans (size_sum _ _ _)) ?andbT //; last first.
  apply/bigmax_leqP=> /= i _; rewrite -polyC_exp coef_map /=.
  have [->|pi_neq0]:= eqVneq p`_i 0; first by rewrite rmorph0 mul0r size_poly0.
  rewrite size_proper_mul ?lead_coefC ?lead_coef_map_eq; last 2 first.
  + rewrite -lead_coef_eq0 lead_coef_mul_monic ?monicXn;
    by rewrite ?(lead_coef_eq0, polyC_eq0).
  + by rewrite ?polyC_eq0 ?lead_coef_eq0.
  rewrite size_polyC size_map_polyC monic_neq0 ?monicXn // addn1 /=.
  by rewrite [(fun i : 'I__ => size p`_i) _ <= _]leq_bigmax.
apply/bigmax_leqP=> i _; apply/leq_sizeP => j; move/leq_sizeP/(_ j (leqnn _)).
rewrite coef_sum (_ : \sum__ _ = \sum_(i < size p) p`_i`_j *: 'X^i).
  rewrite -(poly_def _ (fun i0 => p`_i0`_ _)); move/polyP/(_ i).
  by rewrite coef_poly ltn_ord coef0.
by apply: eq_bigr=> k _; rewrite -polyC_exp !(coef_map, coefMC) mul_polyC.
Qed.

Lemma leq_size_evalX (R : ringType) (p : {poly {poly R}}) :
  size p.['X] <= sizeY p + (size p).-1.
Proof.
rewrite horner_coef (leq_trans (size_sum _ _ _)) //.
unlock sizeY; apply/bigmax_leqP=> i _.
rewrite (leq_trans (size_mul _ _)) // size_polyXn addnS leq_add //=.
  by rewrite [(fun i : 'I__  => size p`_i) i <= _]leq_bigmax.
by case: size i=> //= [[] //|n i]; rewrite leq_ord.
Qed.

Lemma leq_size_coef (R : comRingType) (p : {poly {poly R}})
  (i : nat) : size p`_i <= sizeY p.
Proof.
unlock sizeY; have [lt_in|ge_in] := ltnP i (size p).
  by rewrite -/((fun i : 'I__ => size p`_i) (Ordinal lt_in)) leq_bigmax.
by rewrite (@leq_trans 0%N) // leqn0 size_poly_eq0 (leq_sizeP _ _ ge_in).
Qed.

Lemma leq_size_lead_coef  (R : comRingType) (p : {poly {poly R}}) :
  size (lead_coef p) <= sizeY p.
Proof. by rewrite lead_coefE leq_size_coef. Qed.

Lemma leq_size_evalC (R : comRingType) (p : {poly {poly R}}) (a : R) :
  size p.[a%:P] <= sizeY p.
Proof.
rewrite horner_coef (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> i _.
rewrite (leq_trans (size_mul _ _)) // -polyC_exp size_polyC.
rewrite (leq_trans _ (leq_size_coef _ i)) //.
by case: eqP; rewrite (addn0, addn1) ?leq_pred.
Qed.

Lemma swapXY_horner (R : comRingType) (p : {poly {poly {poly R}}})
  (q : {poly {poly R}}): swapXY (p.[q]) = (p ^ (@swapXY _)).[swapXY q].
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite !(horner0, rmorph0).
rewrite !horner_coef rmorph_sum.
rewrite size_map_poly_id0 ?swapXY_eq0 ?lead_coef_eq0 //.
by apply: eq_big=> //= i _; rewrite rmorphM rmorphX coef_map.
Qed.

Lemma horner2_swapXY (R : comRingType) (p : {poly {poly R}})
  (x y : R) : (swapXY p).[x, y] = p.[y, x].
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite !(horner0, rmorph0).
rewrite (@horner_coef_wide _ (size p)); last first.
  by rewrite (leq_trans (leq_size_evalC _ _)) // sizeYE swapXYK.
rewrite horner_coef -sizeYE.
transitivity  (\sum_(i < size p)
      (\sum_(j < sizeY p) ((swapXY p)`_j * x%:P ^+ j)`_i * y ^+ i)).
  by apply: eq_big=> //= i _; rewrite coef_sum mulr_suml.
rewrite exchange_big (@horner_coef_wide _ (sizeY p)) ?leq_size_evalC //=.
rewrite horner_coef; apply: eq_big=> //= i _.
rewrite coef_sum -mulr_suml; apply: eq_big=> //= j _.
by rewrite -!polyC_exp !coefMC coef_swapXY mulrAC.
Qed.

Definition poly_XaY (R : ringType) (p : {poly R}) := p ^ polyC \Po ('X + 'Y).
Definition poly_XmY (R : ringType) (p : {poly R}) := p ^ polyC \Po ('X * 'Y).

Lemma swapXY_poly_XaY (R : comRingType) (p : {poly R}) :
  swapXY (poly_XaY p) = (poly_XaY p).
Proof.
rewrite /poly_XaY /comp_poly swapXY_horner -!map_comp_poly /=.
congr _.[_]; last by rewrite rmorphD /= swapXY_polyC map_polyX swapXY_X addrC.
by apply: eq_map_poly=> q /=; rewrite swapXY_polyC map_polyC.
Qed.

Lemma swapXY_poly_XmY (R : comRingType) (p : {poly R}) :
  swapXY (poly_XmY p) = (poly_XmY p).
Proof.
rewrite /poly_XmY /comp_poly swapXY_horner -!map_comp_poly /=.
congr _.[_]; last by rewrite rmorphM /= swapXY_polyC map_polyX swapXY_X mulrC.
by apply: eq_map_poly=> q /=; rewrite swapXY_polyC map_polyC.
Qed.

Lemma horner_poly_XaY (R : comRingType) (p : {poly R}) (x : {poly R}) :
  (poly_XaY p).[x] = p \Po (x + 'X).
Proof. by rewrite horner_comp_poly !horner_lin. Qed.

Lemma horner_poly_XmY (R : comRingType) (p : {poly R}) (x : {poly R}) :
  (poly_XmY p).[x] = p \Po (x * 'X).
Proof. by rewrite horner_comp_poly !horner_lin. Qed.

Lemma poly_XaY0 (R : ringType) : poly_XaY (0 : {poly R}) = 0.
Proof. by rewrite /poly_XaY rmorph0 poly_com0p. Qed.

Lemma size_poly_XaY (R : idomainType) (p : {poly R}) :
  size (poly_XaY p) = size p.
Proof. by rewrite size_comp_poly2 ?size_addXr // size_map_polyC. Qed.

Lemma poly_XaY_eq0 (R : idomainType) (p : {poly R}) :
  (poly_XaY p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_poly_XaY. Qed.

Lemma size_poly_XmY (R : idomainType) (p : {poly R}) :
  size (poly_XmY p) = size p.
Proof. by rewrite size_comp_poly2 ?size_mulXr ?polyX_eq0 ?size_map_polyC. Qed.

Lemma poly_XmY_eq0 (R : idomainType) (p : {poly R}) :
  (poly_XmY p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_poly_XmY. Qed.

Lemma lead_coef_poly_XaY (R : idomainType) (p : {poly R}) :
  lead_coef (poly_XaY p) = (lead_coef p)%:P.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite !poly_XaY0 !lead_coef0.
rewrite lead_coefE size_poly_XaY.
rewrite /poly_XaY /comp_poly horner_coef !size_map_polyC.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //=.
rewrite coef_sum big_ord_recr /= big1; last first.
  move=> i _; rewrite !coef_map coefCM addrC exprn_addl coef_sum big1 ?mulr0 //.
  move=> /= j _; rewrite coefMn -polyC_exp coefCM coefXn.
  by rewrite gtn_eqF ?mulr0 ?mul0rn // (leq_ltn_trans (leq_ord _)).
rewrite add0r !coef_map -lead_coefE coefCM /=.
rewrite addrC exprn_addl /= coef_sum big_ord_recr /= big1; last first.
  move=> /= i _; rewrite -polyC_exp coefMn coefCM coefXn.
  by rewrite gtn_eqF // mulr0 mul0rn.
by rewrite binn subnn add0r expr0 mul1r mulr1n coefXn eqxx mulr1.
Qed.

End swapXY.
Implicit Arguments swapXY [[R]].

Section poly_field_resultant.

Definition annul_sub (R : ringType) (p q : {poly R}) :=
  nosimpl (resultant (poly_XaY p) (q ^ polyC)).

Lemma has_root_size_gt1 (R : ringType) (a : R) (p : {poly R}) :
  (p != 0)%B -> root p a -> 1 < size p.
Proof.
move=> p_neq0 rootpa.
rewrite ltnNge leq_eqVlt ltnS leqn0 size_poly_eq0 (negPf p_neq0) orbF.
by apply: contraL rootpa=> /size1P [c c_neq0 ->]; rewrite rootE hornerC.
Qed.

Lemma annul_sub_in_ideal (R : idomainType) (p q : {poly R}) :
  1 < size p -> 1 < size q ->
  {uv : {poly {poly R}} * {poly {poly R}} |
    size uv.1 < size q /\ size uv.2 < size p &
    forall x y, (annul_sub p q).[y] = uv.1.[x%:P].[y] * p.[x + y]
                                      + uv.2.[x%:P].[y] * q.[x]}.
Proof.
move=> hsp hsq; rewrite /annul_sub; set p' := poly_XaY _; set q' := q ^ _.
have [||[u v] /= []] := @resultant_in_ideal _ p' q';
  rewrite ?size_poly_XaY ?size_map_polyC //.
move=> hup hvq hres; exists (u, v)=> // x y.
move: hres=> /(f_equal (eval x%:P)); rewrite /eval hornerC=> -> /=.
by rewrite !{1}(horner_poly_XaY, horner_lin, horner_comp_poly).
Qed.

Lemma annul_subP (F : idomainType) (p q : {poly F}) (a b : F) :
  p != 0 -> q != 0 -> p.[a] = 0 -> q.[b] = 0 ->
  (annul_sub p q).[a - b] = 0.
Proof.
move=> p_neq0 q_neq0 pa0 pb0.
have [||[u v] /= [hu hv] huv] := @annul_sub_in_ideal _ p q.
+ by rewrite (@has_root_size_gt1 _ a) //; apply/rootP.
+ by rewrite (@has_root_size_gt1 _ b) //; apply/rootP.
by rewrite (huv b) addrCA subrr addr0 pa0 pb0 !mulr0 addr0.
Qed.

Lemma annul_sub_iotaP (F F' : fieldType) (p q : {poly F}) (a b : F')
  (iota : {rmorphism F -> F'}) : p != 0 -> q != 0 ->
  (p ^ iota).[a] = 0 -> (q ^ iota).[b] = 0 ->
  ((annul_sub p q) ^ iota).[a - b] = 0.
Proof.
move=> p_neq0 q_neq0 pa0 pb0; rewrite /annul_sub /= map_resultant;
  do ?by rewrite ?(comp_poly2_eq0, size_addXr, map_poly_eq0, lead_coef_eq0).
rewrite /comp_poly /= -!map_comp_poly /=.
have hYaX : 'X + 'Y = ('X + 'Y) ^ (map_poly iota) :> {poly {poly F'}}.
  by rewrite rmorphD /= map_polyC /= !map_polyX.
rewrite -horner_map /= -hYaX -!map_comp_poly /=.
rewrite (eq_map_poly (map_polyC _)) [q ^ _]map_comp_poly /=.
rewrite (@eq_map_poly _ _ _ ((polyC \o polyC) \o iota)); last first.
  by move=> x /=; rewrite map_polyC /= map_polyC.
by rewrite !map_comp_poly /= -/(_ \Po _) annul_subP ?map_poly_eq0.
Qed.


Lemma annul_sub_neq0 (F : fieldType) (p q : {poly F}) :
  p != 0 -> q != 0 -> annul_sub p q != 0.
Proof.
move=> p_neq0 q_neq0; rewrite /annul_sub.
set p' := poly_XaY _; set q' := _ ^ _.
have p'_neq0 : p' != 0 by rewrite poly_XaY_eq0.
have q'_neq0 : q' != 0 by rewrite map_polyC_eq0.
rewrite resultant_eq0 -leqNgt leq_eqVlt ltnS leqn0; apply/orP; left.
have [// | ] := boolP (coprimep p' q').
case/(bezout_coprimepPn p'_neq0 q'_neq0) => [[u v]] /=.
case/and3P=> /andP [u_gt0 ltn_uq] v_gt0 ltn_vp hpq.
have u_neq0 : u != 0 by rewrite -size_poly_gt0.
have v_neq0 : v != 0 by rewrite -size_poly_gt0.
move: (hpq)=> /(f_equal ((size \o (lead_coef \o swapXY)))) /=.
rewrite 2!{1}rmorphM 2!{1}lead_coef_Imul /=.
rewrite !{1}size_mul_id ?{1}lead_coef_eq0 ?{1}swapXY_eq0;
  do ?by rewrite (p'_neq0, q'_neq0, u_neq0, v_neq0).
rewrite swapXY_map_polyC lead_coefC swapXY_poly_XaY -/p'.
rewrite lead_coef_poly_XaY size_polyC lead_coef_eq0 p_neq0 {1}addn1 /=.
rewrite -[X in (X + _).-1]prednK ?addSn /=; last first.
  by rewrite lt0n size_poly_eq0 lead_coef_eq0 swapXY_eq0.
move=> huvq; have := leq_size_lead_coef (swapXY u).
rewrite huvq sizeYE swapXYK=> /leq_ltn_trans /(_ ltn_uq).
by rewrite size_map_poly addnC ltn_add_sub subnn.
Qed.

Definition annul_div (R : ringType) (p q : {poly R}) :=
  nosimpl (resultant (poly_XmY p) (q ^ polyC)).

Lemma factor_poly (R : ringType) (p : {poly R}) (x : R) : p != 0 ->
  root p x -> {d : {poly R} | 0 < size d < size p & p = d * ('X - x%:P)}.
Proof.
move=> p_neq0 rpx; apply: sig2_eqW; move: rpx; rewrite -RPdiv.rdvdp_factorl.
case/RPdiv.mon.rdvdpP=> [|d hp]; first by rewrite monic_factor.
exists d=> //; move: p_neq0; rewrite hp=> {p hp} hp.
move: hp; have [->|d_neq0 hp] := eqVneq d 0; first by rewrite mul0r eqxx.
rewrite size_proper_mul; last by rewrite lead_coef_factor mulr1 lead_coef_eq0.
by rewrite size_factor addn2 ltnS leqnn lt0n size_poly_eq0 d_neq0.
Qed.

Lemma annul_div_in_ideal (R : idomainType) (p q : {poly R}) :
  1 < size p -> 1 < size q ->
  {uv : {poly {poly R}} * {poly {poly R}} |
    size uv.1 < size q /\ size uv.2 < size p &
    forall x y, (annul_div p q).[y] = uv.1.[x%:P].[y] * p.[x * y]
                                      + uv.2.[x%:P].[y] * q.[x]}.
Proof.
move=> hsp hsq; rewrite /annul_div; set p' := poly_XmY _; set q' := q ^ _.
have [||[u v] /= []] := @resultant_in_ideal _ p' q';
  rewrite ?size_poly_XmY ?size_map_polyC //.
move=> hup hvq hres; exists (u, v)=> // x y.
move: hres=> /(f_equal (eval x%:P)); rewrite /eval hornerC=> -> /=.
by rewrite !{1}(horner_poly_XmY, horner_lin, horner_comp_poly).
Qed.

Lemma annul_divP (F : fieldType) (p q : {poly F}) (a b : F) :
  p != 0 -> q != 0 -> b != 0 ->
  p.[a] = 0 -> q.[b] = 0 -> (annul_div p q).[a / b] = 0.
Proof.
move=> p_neq0 q_neq0 b_neq0 pa0 pb0.
have [||[u v] /= [hu hv] huv] := @annul_div_in_ideal _ p q.
+ by rewrite (@has_root_size_gt1 _ a) //; apply/rootP.
+ by rewrite (@has_root_size_gt1 _ b) //; apply/rootP.
by rewrite (huv b) mulrCA divff // mulr1 pa0 pb0 !mulr0 addr0.
Qed.

Lemma annul_div_iotaP (F F' : fieldType) (p q : {poly F}) (a b : F')
  (iota : {rmorphism F -> F'}) : p != 0 -> q != 0 -> b != 0 ->
  (p ^ iota).[a] = 0 -> (q ^ iota).[b] = 0 ->
  ((annul_div p q) ^ iota).[a / b] = 0.
Proof.
move=> p_neq0 q_neq0 b_neq0 pa0 pb0; rewrite /annul_div /= map_resultant;
  do ?by rewrite ?(comp_poly2_eq0, size_mulXr,
    map_poly_eq0, lead_coef_eq0, polyX_eq0).
rewrite /comp_poly /= -!map_comp_poly /=.
have hYmX : 'X * 'Y = ('X * 'Y) ^ (map_poly iota) :> {poly {poly F'}}.
  by rewrite rmorphM /= map_polyC /= !map_polyX.
rewrite -horner_map /= -hYmX -!map_comp_poly /=.
rewrite (eq_map_poly (map_polyC _)) [q ^ _]map_comp_poly /=.
rewrite (@eq_map_poly _ _ _ ((polyC \o polyC) \o iota)); last first.
  by move=> x /=; rewrite map_polyC /= map_polyC.
by rewrite !map_comp_poly /= -/(_ \Po _) annul_divP ?map_poly_eq0.
Qed.

Lemma size_mulX (R : ringType) (p : {poly R}) :
  p != 0 -> size (p * 'X) = (size p).+1.
Proof. by move=> ?; rewrite size_mul_monic ?monicX // size_polyX addn2. Qed.

Lemma size_swap_mulX  (R : idomainType) (p : {poly {poly R}}) :
  size (swapXY (p * 'X)) = size (swapXY p).
Proof. by rewrite rmorphM mulrC /= swapXY_X size_polyC_mul ?polyX_eq0. Qed.

Lemma dvdXp (R : idomainType) (p : {poly R}) : 'X %| p = root p 0.
Proof. by rewrite -dvdp_factorl subr0. Qed.

Lemma annul_div_neq0 (F : fieldType) (p q : {poly F}) :
  p != 0 -> q.[0] != 0 -> annul_div p q != 0.
Proof.
move=> p_neq0 q0_neq0; rewrite /annul_div.
rewrite resultant_eq0 -leqNgt leq_eqVlt ltnS leqn0; apply/orP; left.
rewrite -coprimep_def; have [//|] := boolP (coprimep _ _).
case/(bezout_coprimepPn _ _); do ?by rewrite poly_XmY_eq0.
  by rewrite map_polyC_eq0; apply: contra q0_neq0=> /eqP ->; rewrite horner0.
move=> [u v] /= /and3P [] /andP [u_neq0 ltn_uq] v_neq0 ltn_vp hpq.
rewrite ?size_map_polyC ?size_poly_XmY in ltn_uq ltn_vp.
rewrite ?size_poly_gt0 in u_neq0 v_neq0.
wlog vX0_neq0 : u v p q p_neq0 q0_neq0 hpq
                u_neq0 ltn_uq v_neq0 ltn_vp / (swapXY v).[0] != 0 => [hwlog|].
  elim : (sizeY v) {-2}v u p q (leqnn (sizeY v)) v_neq0 u_neq0
     p_neq0 q0_neq0 ltn_vp ltn_uq hpq => {v} /= [|sv ihsv] v u p q.
    by rewrite leqn0 sizeYE ?size_poly_eq0 swapXY_eq0=> ->.
  move=> hsv v_neq0 u_neq0 p_neq0 q0_neq0 ltn_vp ltn_uq hpq.
  have [vX0_eq0|] := eqVneq (swapXY v).[0] 0; last exact: (hwlog u v p q).
  move: (vX0_eq0)=> /eqP /factor_poly []; first by rewrite swapXY_eq0.
  move=> v' /andP []; rewrite size_poly_gt0 subr0=> v'_neq0 hsv' swv.
  move: (hpq)=> /(f_equal (size \o (eval 0 \o swapXY))) /= => /eqP.
  rewrite !{1}rmorphM /= /eval swapXY_map_polyC hornerC.
  rewrite swapXY_poly_XmY horner_comp_poly !horner_lin horner_map /=.
  rewrite vX0_eq0 mul0r size_poly0 size_poly_eq0 mulf_eq0 polyC_eq0.
  have [/eqP p0_eq0|p0_neq0] := boolP (p.[0] == 0); rewrite (orbT, orbF).
    move=> _; move: (hpq)=> /(f_equal (size \o (eval 0%:P))) /= => /eqP.
    rewrite !{1}rmorphM /= /eval.
    rewrite horner_map /= horner_poly_XmY mul0r comp_poly0 -horner_coef0.
    rewrite p0_eq0 mulr0 size_poly0 eq_sym size_poly_eq0 mulf_eq0 !polyC_eq0.
    rewrite (negPf q0_neq0) orbF -[v]swapXYK swv rmorphM /= horner_mul.
    rewrite swapXY_X hornerC mulf_eq0 polyX_eq0 orbF -rootE.
    case/factor_poly=> [|v'' /andP []]; first by rewrite swapXY_eq0.
    rewrite size_poly_gt0 !polyC0 {1}subr0=> v''_neq0 hsv'' swv'.
    move: (p0_eq0)=> /rootP/factor_poly; move /(_ p_neq0) => [p' /andP[]].
    rewrite size_poly_gt0 polyC0 {1}subr0=> p'_neq0 hsp' hp.
    apply: (ihsv v'' u p' q);
    do ?by rewrite (p'_neq0, q0_neq0, u_neq0, v''_neq0, swapXY_eq0, ltn_uq).
    + rewrite -ltnS (leq_trans _ hsv) // !sizeYE (leq_trans _ hsv') // ltnS.
      by rewrite -[v']swapXYK swv' size_swap_mulX leqnn.
    + rewrite -ltnS -size_mulX // -[X in _ < X]size_mulX // -swv' -hp.
      rewrite (leq_trans _ ltn_vp) // ltnS -[v]swapXYK swv.
      by rewrite [X in _ <= X]size_swap_mulX leqnn.
    move: hpq; rewrite -[v]swapXYK swv !{1}rmorphM /= swv' swapXY_X.
    rewrite hp /poly_XmY !rmorphM /= !map_polyX poly_comXp.
    rewrite mulrA -[X in _ =  X * _ -> _]mulrA [X in _ = X -> _]mulrAC.
    by move/mulIf; apply; rewrite mulf_eq0 negb_or polyC_eq0 !polyX_eq0.
  move=> /factor_poly []; first by rewrite swapXY_eq0.
  move=> u' /andP [u'_neq0 hsu']; rewrite subr0=> swu.
  rewrite !size_poly_gt0 in u'_neq0 v'_neq0.
  apply: (ihsv (swapXY v') (swapXY u') p q);
    do ?[by rewrite (p_neq0, q0_neq0)|by rewrite swapXY_eq0].
  + by rewrite sizeYE swapXYK -ltnS (leq_trans _ hsv) ?sizeYE.
  + by rewrite (leq_trans _ ltn_vp) // ltnS -[v]swapXYK swv size_swap_mulX.
  + by rewrite (leq_trans _ ltn_uq) // ltnS -[u]swapXYK swu size_swap_mulX.
  move: hpq; rewrite -[u]swapXYK -[v]swapXYK swu swv 2!{1}rmorphM.
  rewrite {1}mulrAC {1}[X in _ = X -> _]mulrAC=> /mulIf; apply.
  by rewrite ?swapXY_eq0 polyX_eq0.
have q_neq0 : q != 0 by apply: contra q0_neq0=> /eqP ->; rewrite horner0.
move: hpq=> /(f_equal (size \o (eval 0 \o swapXY))) /=.
rewrite !{1}rmorphM /= /eval swapXY_map_polyC hornerC.
rewrite swapXY_poly_XmY horner_comp_poly !horner_lin horner_map /=.
have [-> /eqP|uX0_neq0] := eqVneq (swapXY u).[0] 0.
  rewrite {1}mul0r size_poly0 eq_sym size_poly_eq0 mulf_eq0.
  by rewrite (negPf vX0_neq0) (negPf q_neq0).
have [-> /eqP|p0_neq0] := eqVneq p.[0] 0.
  rewrite {1}mulr0 size_poly0 eq_sym size_poly_eq0 mulf_eq0.
  by rewrite (negPf vX0_neq0) (negPf q_neq0).
rewrite !{1}size_mul_id ?polyC_eq0 // size_polyC p0_neq0 {1}addn1 /=.
rewrite -[X in (X + _).-1]prednK ?addSn /=; last first.
  by rewrite lt0n size_poly_eq0 vX0_neq0.
move=> huvq; have := leq_size_coef (swapXY u) 0%N.
rewrite -horner_coef0 huvq sizeYE swapXYK=> /leq_ltn_trans /(_ ltn_uq).
by rewrite ltnNge leq_addl.
Qed.

End poly_field_resultant.