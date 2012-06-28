Require Import ssreflect ssrfun ssrbool choice eqtype ssrnat seq div fintype.
Require Import tuple finfun bigop fingroup perm ssralg zmodp matrix mxalgebra.
Require Import poly polydiv mxpoly binomial.
Local Open Scope ring_scope.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Notation "'Y" := 'X%:P : ring_scope.

Notation "p .[ x , y ]" := (p.[x%:P].[y])
  (at level 2, left associativity, format "p .[ x ,  y ]") : ring_scope.

Local Notation eval := horner_eval.

Section swapXY.

Fact swapXY_key : unit. Proof. by []. Qed.
Definition swapXY_def (R : ringType) (p : {poly {poly R}}) : {poly {poly R}} :=
  (p ^ map_poly polyC).['Y].
Definition swapXY := locked_with swapXY_key swapXY_def.
Canonical swapXY_unlockable := [unlockable fun swapXY].
Implicit Arguments swapXY [[R]].

Lemma swapXY_is_additive (R : ringType) : additive (@swapXY R).
Proof. by move=> p q; rewrite unlock rmorphB !hornerE. Qed.
Canonical swapXY_addf R := Additive (@swapXY_is_additive R).

Lemma swapXY_is_multiplicative (R : comRingType) : multiplicative (@swapXY R).
Proof. by split=> [p q|]; rewrite unlock (rmorph1, rmorphM) !hornerE. Qed.
Canonical swapXY_rmorph R := AddRMorphism (@swapXY_is_multiplicative R).

Lemma swapXY_X (R : ringType) : swapXY 'X = 'Y :> {poly {poly R}}.
Proof. by rewrite unlock map_polyX hornerX. Qed.

Lemma swapXY_polyC (R : ringType) (p : {poly R}) : swapXY p%:P = p ^ polyC.
Proof. by rewrite unlock map_polyC /= hornerC. Qed.

Lemma swapXY_Y (R : ringType) : swapXY 'Y = 'X :> {poly {poly R}}.
Proof. by rewrite swapXY_polyC map_polyX. Qed.

Lemma coef_swapXY (R : ringType) p i j : (swapXY p)`_i`_j = p`_j`_i :> R.
Proof.
elim/poly_ind: p => [|p c IHp] in i j *; first by rewrite raddf0 !coef0.
rewrite raddfD !coefD /= swapXY_polyC coef_map /= !coefC coefMX.
rewrite !(fun_if (fun q : {poly _} => q`_i)) coef0 -IHp; congr (_ + _).
by rewrite unlock rmorphM /= map_polyX hornerMX coefMC coefMX.
Qed.

Lemma swapXY_map (R1 R2 : ringType) (nu : {additive R1 -> R2}) p :
  swapXY (p ^ map_poly nu) = swapXY p ^ map_poly nu.
Proof.
by apply/polyP=> i; apply/polyP=> j; rewrite !(coef_map, coef_swapXY).
Qed.

Lemma swapXYK (R : ringType) : involutive (@swapXY R).
Proof. by move => p; do 2![apply/polyP=> ?]; rewrite !coef_swapXY. Qed.

Lemma swapXY_map_polyC (R : ringType) (p : {poly R}) :
  swapXY (p ^ polyC) = p%:P.
Proof. by rewrite -swapXY_polyC swapXYK. Qed.

Lemma swapXY_eq0 (R : ringType) (p : {poly {poly R}}) :
  (swapXY p == 0) = (p == 0).
Proof. by rewrite (inv_eq (@swapXYK R)) raddf0. Qed.

Definition sizeY (R : ringType) (p : {poly {poly R}}) : nat :=
  \max_(i < size p) (size p`_i).

(* more general version of sizeY *)
Lemma sizeYE (R : ringType) (p : {poly {poly R}}) :
  sizeY p = size (swapXY p).
Proof.
have [->|p_neq0] := eqVneq p 0.
  by rewrite swapXY_polyC rmorph0 /sizeY size_poly0 big_ord0.
rewrite unlock /sizeY horner_coef.
rewrite size_map_poly_id0 ?map_polyC_eq0 ?lead_coef_eq0 //.
apply/eqP; rewrite eqn_leq (leq_trans (size_sum _ _ _)) ?andbT //; last first.
  apply/bigmax_leqP=> /= i _; rewrite -polyC_exp coef_map /=.
  have [->|pi_neq0]:= eqVneq p`_i 0; first by rewrite rmorph0 mul0r size_poly0.
  rewrite size_proper_mul ?lead_coefC ?lead_coef_map_eq; last 2 first.
  + rewrite -lead_coef_eq0 lead_coef_Mmonic ?monicXn;
    by rewrite ?(lead_coef_eq0, polyC_eq0).
  + by rewrite ?polyC_eq0 ?lead_coef_eq0.
  rewrite size_polyC size_map_polyC monic_neq0 ?monicXn // addn1 /=.
  by rewrite (bigmax_sup i).
apply/bigmax_leqP=> i _; apply/leq_sizeP => j; move/leq_sizeP/(_ j (leqnn _)).
rewrite coef_sum (_ : \sum__ _ = \sum_(i < size p) p`_i`_j *: 'X^i).
  rewrite -(poly_def _ (fun i0 => p`_i0`_ _)); move/polyP/(_ i).
  by rewrite coef_poly ltn_ord coef0.
by apply: eq_bigr=> k _; rewrite -polyC_exp !(coef_map, coefMC) mul_polyC.
Qed.

Lemma leq_size_evalX (R : ringType) (p : {poly {poly R}}) :
  size p.['X] <= sizeY p + (size p).-1.
Proof.
rewrite horner_coef (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> i _.
rewrite (leq_trans (size_mul_leq _ _)) // size_polyXn addnS leq_add //=.
  by rewrite (bigmax_sup i).
by case: size i=> //= [[] //|n i]; rewrite leq_ord.
Qed.

Lemma leq_size_coef (R : ringType) (p : {poly {poly R}})
  (i : nat) : size p`_i <= sizeY p.
Proof.
unlock sizeY; have [lt_in|ge_in] := ltnP i (size p).
  by rewrite (bigmax_sup (Ordinal lt_in)).
by rewrite (@leq_trans 0%N) // leqn0 size_poly_eq0 (leq_sizeP _ _ ge_in).
Qed.

Lemma leq_size_lead_coef  (R : ringType) (p : {poly {poly R}}) :
  size (lead_coef p) <= sizeY p.
Proof. by rewrite lead_coefE leq_size_coef. Qed.

Lemma leq_size_evalC (R : ringType) (p : {poly {poly R}}) (a : R) :
  size p.[a%:P] <= sizeY p.
Proof.
rewrite horner_coef (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> i _.
rewrite (leq_trans (size_mul_leq _ _)) // -polyC_exp size_polyC.
rewrite (leq_trans _ (leq_size_coef _ i)) //.
by case: eqP; rewrite (addn0, addn1) ?leq_pred.
Qed.

Lemma swapXY_horner (R : comRingType) (p : {poly {poly {poly R}}})
  (q : {poly {poly R}}): swapXY (p.[q]) = (p ^ (@swapXY _)).[swapXY q].
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite !(horner0, raddf0).
rewrite !horner_coef raddf_sum size_map_poly_id0 ?swapXY_eq0 ?lead_coef_eq0 //.
by apply: eq_bigr => i _; rewrite /= rmorphM rmorphX coef_map.
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
  by apply: eq_big=> //= i _; rewrite coef_sum -mulr_suml.
rewrite exchange_big (@horner_coef_wide _ (sizeY p)) ?leq_size_evalC //=.
rewrite horner_coef; apply: eq_big=> //= i _.
rewrite coef_sum mulr_suml; apply: eq_big=> //= j _.
by rewrite -!polyC_exp !coefMC coef_swapXY mulrAC.
Qed.

Lemma horner_swapXY (R : comRingType) (p : {poly {poly R}}) (x : R) :
  (swapXY p).[x%:P] = (p ^ (eval x)).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite !(horner0, rmorph0).
apply/polyP=> i /=; rewrite coef_map /= /eval horner_coef coef_sum -sizeYE.
rewrite (@horner_coef_wide _ (sizeY p)); last first.
  have [hi|hi] := leqP (size p) i; first by rewrite nth_default ?size_poly0.
  exact: leq_bigmax (Ordinal hi).
by apply: eq_big=> // j _; rewrite -polyC_exp coefMC coef_swapXY.
Qed.

Lemma horner_polyC (R : comRingType) (p : {poly {poly R}}) x :
  p.[x%:P] = ((swapXY p) ^ (eval x)).
Proof. by rewrite -horner_swapXY swapXYK. Qed.

Lemma swapXY_map_poly2 (R R' : comRingType) (p : {poly {poly R}})
(f : {rmorphism  R -> R'}) : swapXY (p ^ map_poly f) = (swapXY p) ^ map_poly f.
Proof.
by apply/polyP=> i; apply/polyP=> j; rewrite !(coef_swapXY, coef_map).
Qed.

Lemma sizeY_eq0 (R : comRingType) (p : {poly {poly R}}) :
  (sizeY p == 0%N) = (p == 0)%B.
Proof. by rewrite sizeYE size_poly_eq0 swapXY_eq0. Qed.

Definition poly_XaY (R : ringType) (p : {poly R}) := p ^ polyC \Po ('X + 'Y).
Definition poly_XmY (R : ringType) (p : {poly R}) := p ^ polyC \Po ('X * 'Y).

Lemma swapXY_poly_XaY (R : comRingType) (p : {poly R}) :
  swapXY (poly_XaY p) = (poly_XaY p).
Proof.
rewrite /poly_XaY /comp_poly swapXY_horner -!map_poly_comp /=.
congr _.[_]; last by rewrite rmorphD /= swapXY_polyC map_polyX swapXY_X addrC.
by apply: eq_map_poly=> q /=; rewrite swapXY_polyC map_polyC.
Qed.

Lemma swapXY_poly_XmY (R : comRingType) (p : {poly R}) :
  swapXY (poly_XmY p) = (poly_XmY p).
Proof.
rewrite /poly_XmY /comp_poly swapXY_horner -!map_poly_comp /=.
congr _.[_]; last by rewrite rmorphM /= swapXY_polyC map_polyX swapXY_X mulrC.
by apply: eq_map_poly=> q /=; rewrite swapXY_polyC map_polyC.
Qed.

Lemma horner_poly_XaY (R : comRingType) (p : {poly R}) (x : {poly R}) :
  (poly_XaY p).[x] = p \Po (x + 'X).
Proof. by rewrite horner_comp !hornerE. Qed.

Lemma horner_poly_XmY (R : comRingType) (p : {poly R}) (x : {poly R}) :
  (poly_XmY p).[x] = p \Po (x * 'X).
Proof. by rewrite horner_comp !hornerE. Qed.

Lemma poly_XaY0 (R : ringType) : poly_XaY (0 : {poly R}) = 0.
Proof. by rewrite /poly_XaY rmorph0 comp_poly0. Qed.

Lemma size_poly_XaY (R : idomainType) (p : {poly R}) :
  size (poly_XaY p) = size p.
Proof. by rewrite size_comp_poly2 ?size_XaddC // size_map_polyC. Qed.

Lemma poly_XaY_eq0 (R : idomainType) (p : {poly R}) :
  (poly_XaY p == 0) = (p == 0).
Proof. by rewrite -!size_poly_eq0 size_poly_XaY. Qed.

Lemma size_poly_XmY (R : idomainType) (p : {poly R}) :
  size (poly_XmY p) = size p.
Proof. by rewrite size_comp_poly2 ?size_XmulC ?polyX_eq0 ?size_map_polyC. Qed.

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
  move=> i _; rewrite !coef_map coefCM addrC exprDn coef_sum big1 ?mulr0 //.
  move=> /= j _; rewrite coefMn -polyC_exp coefCM coefXn.
  by rewrite gtn_eqF ?mulr0 ?mul0rn // (leq_ltn_trans (leq_ord _)).
rewrite add0r !coef_map -lead_coefE coefCM /=.
rewrite addrC exprDn /= coef_sum big_ord_recr /= big1; last first.
  move=> /= i _; rewrite -polyC_exp coefMn coefCM coefXn.
  by rewrite gtn_eqF // mulr0 mul0rn.
by rewrite binn subnn add0r expr0 mul1r mulr1n coefXn eqxx mulr1.
Qed.

End swapXY.
Implicit Arguments swapXY [[R]].

Section PolyXYalgebraic.
(* These results subsume the two specific resultant constructions below, but  *)
(* are already subsumed by the integralOver development in mxpoly.            *)

Variables (F E : fieldType) (FtoE : {rmorphism F -> E}).

Lemma algebraic_root_polyXY x y :
    (let pEx p := (map_poly (map_poly FtoE) p).[x%:P] in
    exists2 p, pEx p != 0 & root (pEx p) y) ->
  algebraicOver FtoE x -> algebraicOver FtoE y.
Proof.
set pEx := (fun _ => _) => [] [p nz_px pxy0] [q nz_q qx0].
have [/size1_polyC Dp | p_gt1] := leqP (size p) 1.
  by rewrite /pEx Dp map_polyC hornerC map_poly_eq0 in nz_px pxy0; exists p`_0.
elim: {q}_.+1 {-2}q (ltnSn (size q)) => // m IHm q le_qm in nz_q qx0 *.
pose q1 := map_poly polyC q; have nz_q1: q1 != 0 by rewrite map_poly_eq0.
have sz_q1: size q1 = size q by rewrite size_map_polyC.
have q_gt1: size q1 > 1.
  by rewrite sz_q1 -(size_map_poly FtoE) (root_size_gt1 _ qx0) ?map_poly_eq0.
have [uv _ Dr] := resultant_in_ideal p_gt1 q_gt1; set r := resultant p _ in Dr.
have q1x0: pEx q1 = 0.
  rewrite /pEx -map_poly_comp (eq_map_poly (map_polyC _)) map_poly_comp.
  by rewrite horner_map (rootP qx0). 
have [|r_nz] := boolP (r == 0); last first.
  exists r; rewrite // -[map_poly _ _](hornerC _ x%:P) -map_polyC Dr rmorphD.
  by rewrite !rmorphM !hornerE -!/(pEx _) q1x0 mulr0 addr0 rootM pxy0 orbT.
have nz_p: p != 0 by rewrite -size_poly_gt0 ltnW.
rewrite resultant_eq0 => /gtn_eqF/Bezout_coprimepPn[]// [q2 p1] /=.
rewrite size_poly_gt0 sz_q1 => /andP[/andP[nz_q2 ltq2] _] Dq.
pose n := (size (lead_coef q2)).-1; pose q3 := map_poly (coefp n) q2.
have nz_q3: q3 != 0 by rewrite map_poly_eq0_id0 ?lead_coef_eq0.
apply: (IHm q3); rewrite ?(leq_ltn_trans (size_poly _ _)) ?(leq_trans ltq2) //.
have /eqP := congr1 pEx Dq; rewrite /pEx !rmorphM !hornerM /= -!/(pEx _).
rewrite q1x0 mulr0 (mulIr_eq0 _ (mulIf nz_px)) => /eqP/polyP/(_ n)/eqP.
rewrite coef0; congr (_ == 0); rewrite /pEx !horner_coef coef_sum.
rewrite size_map_poly !size_map_poly_id0 ?map_poly_eq0 ?lead_coef_eq0 //.
by apply: eq_bigr => i _; rewrite -rmorphX coefMC !coef_map.
Qed.

Lemma algebraic_sub x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x - y).
Proof.
case=> [p nz_p px0]; apply: algebraic_root_polyXY => pEy.
pose p1 := map_poly polyC p \Po ('X + 'Y).
have p1Ey: pEy p1 = map_poly FtoE p \Po ('X + y%:P).
  rewrite /pEy map_comp_poly rmorphD /= map_polyC /= !map_polyX horner_comp.
  rewrite !hornerE addrC -map_poly_comp.
  by rewrite (eq_map_poly (map_polyC _)) map_poly_comp.
exists p1; rewrite p1Ey; last by rewrite rootE horner_comp !hornerE subrK.
by rewrite comp_poly2_eq0 ?size_XaddC ?map_poly_eq0.
Qed.

Lemma algebraic_id x : algebraicOver FtoE (FtoE x).
Proof.
by exists ('X - x%:P); rewrite ?polyXsubC_eq0 // fmorph_root root_XsubC.
Qed.

Lemma algebraic0 : algebraicOver FtoE 0.
Proof. by rewrite -(rmorph0 FtoE); apply: algebraic_id. Qed.

Lemma algebraic1 : algebraicOver FtoE 1.
Proof. by rewrite -(rmorph1 FtoE); apply: algebraic_id. Qed.

Lemma algebraic_add x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x + y).
Proof.
move=> algFx algFy; rewrite -[y]opprK -(sub0r y) -(subrr y).
by do !apply: algebraic_sub.
Qed.

Lemma algebraic_div x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x / y).
Proof.
move=> [p nz_p px0]; have [-> _ | nz_y] := eqVneq y 0.
  by rewrite invr0 mulr0; apply: algebraic0.
apply: algebraic_root_polyXY => pEy.
pose p1 := map_poly polyC p \Po ('Y * 'X).
have p1Ey: pEy p1 = map_poly FtoE p \Po (y *: 'X).
  rewrite /pEy map_comp_poly horner_comp rmorphM /= map_polyC /= !map_polyX.
  rewrite !hornerE mulrC mul_polyC -map_poly_comp.
  by rewrite (eq_map_poly (map_polyC _)) map_poly_comp.
exists p1; rewrite p1Ey; last first. 
  by rewrite rootE horner_comp hornerZ hornerX mulrC divfK.
by rewrite comp_poly2_eq0 ?map_poly_eq0 ?size_scale ?size_polyX.
Qed.

Lemma algebraic_mul x y :
  algebraicOver FtoE x -> algebraicOver FtoE y -> algebraicOver FtoE (x * y).
Proof.
move=> algFx algFy; rewrite -[y]invrK -[y^-1]mul1r.
by do 2!apply: algebraic_div => //; apply: algebraic1.
Qed.

End PolyXYalgebraic.

Section poly_field_resultant.

Definition annul_sub (R : ringType) (p q : {poly R}) :=
  nosimpl (resultant (poly_XaY p) (q ^ polyC)).

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
by rewrite !{1}(horner_poly_XaY, hornerE, horner_comp).
Qed.

Lemma annul_subP (F : idomainType) (p q : {poly F}) (a b : F) :
  p != 0 -> q != 0 -> p.[a] = 0 -> q.[b] = 0 ->
  (annul_sub p q).[a - b] = 0.
Proof.
move=> p_neq0 q_neq0 pa0 pb0.
have [||[u v] /= [hu hv] huv] := @annul_sub_in_ideal _ p q.
+ by rewrite (@root_size_gt1 _ a) //; apply/rootP.
+ by rewrite (@root_size_gt1 _ b) //; apply/rootP.
by rewrite (huv b) addrCA subrr addr0 pa0 pb0 !mulr0 addr0.
Qed.

Lemma annul_sub_iotaP (F F' : fieldType) (p q : {poly F}) (a b : F')
  (iota : {rmorphism F -> F'}) : p != 0 -> q != 0 ->
  (p ^ iota).[a] = 0 -> (q ^ iota).[b] = 0 ->
  ((annul_sub p q) ^ iota).[a - b] = 0.
Proof.
move=> p_neq0 q_neq0 pa0 pb0; rewrite /annul_sub /= map_resultant;
  do ?by rewrite ?(comp_poly2_eq0, size_XaddC, map_poly_eq0, lead_coef_eq0).
rewrite /comp_poly /= -!map_poly_comp /=.
have hYaX : 'X + 'Y = ('X + 'Y) ^ (map_poly iota) :> {poly {poly F'}}.
  by rewrite rmorphD /= map_polyC /= !map_polyX.
rewrite -horner_map /= -hYaX -!map_poly_comp /=.
rewrite (eq_map_poly (map_polyC _)) [q ^ _]map_poly_comp /=.
rewrite (@eq_map_poly _ _ _ ((polyC \o polyC) \o iota)); last first.
  by move=> x /=; rewrite map_polyC /= map_polyC.
by rewrite !map_poly_comp /= -/(_ \Po _) annul_subP ?map_poly_eq0.
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
case/(Bezout_coprimepPn p'_neq0 q'_neq0) => [[u v]] /=.
case/and3P=> /andP [u_gt0 ltn_uq] v_gt0 ltn_vp hpq.
have u_neq0 : u != 0 by rewrite -size_poly_gt0.
have v_neq0 : v != 0 by rewrite -size_poly_gt0.
move: (hpq)=> /(f_equal ((size \o (lead_coef \o swapXY)))) /=.
rewrite 2!{1}rmorphM 2!{1}lead_coefM /=.
rewrite !{1}size_mul ?{1}lead_coef_eq0 ?{1}swapXY_eq0;
  do ?by rewrite (p'_neq0, q'_neq0, u_neq0, v_neq0).
rewrite swapXY_map_polyC lead_coefC swapXY_poly_XaY -/p'.
rewrite lead_coef_poly_XaY size_polyC lead_coef_eq0 p_neq0 {1}addn1 /=.
rewrite -[X in (X + _).-1]prednK ?addSn /=; last first.
  by rewrite lt0n size_poly_eq0 lead_coef_eq0 swapXY_eq0.
move=> huvq; have := leq_size_lead_coef (swapXY u).
rewrite huvq sizeYE swapXYK=> /leq_ltn_trans /(_ ltn_uq).
by rewrite size_map_poly addnC -ltn_subRL subnn.
Qed.

Definition annul_div (R : ringType) (p q : {poly R}) :=
  nosimpl (resultant (poly_XmY p) (q ^ polyC)).

Lemma factor_poly (R : ringType) (p : {poly R}) (x : R) : p != 0 ->
  root p x -> {d : {poly R} | 0 < size d < size p & p = d * ('X - x%:P)}.
Proof.
move=> p_neq0 rpx; apply: sig2_eqW; move: rpx; rewrite -Pdiv.Ring.rdvdp_XsubCl.
case/Pdiv.RingMonic.rdvdpP=> [|d hp]; first by rewrite monicXsubC.
exists d=> //; move: p_neq0; rewrite hp=> {p hp} hp.
move: hp; have [->|d_neq0 hp] := eqVneq d 0; first by rewrite mul0r eqxx.
rewrite size_proper_mul; last by rewrite lead_coefXsubC mulr1 lead_coef_eq0.
by rewrite size_XsubC addn2 ltnS leqnn lt0n size_poly_eq0 d_neq0.
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
by rewrite !{1}(horner_poly_XmY, hornerE, horner_comp).
Qed.

Lemma annul_divP (F : fieldType) (p q : {poly F}) (a b : F) :
  p != 0 -> q != 0 -> b != 0 ->
  p.[a] = 0 -> q.[b] = 0 -> (annul_div p q).[a / b] = 0.
Proof.
move=> p_neq0 q_neq0 b_neq0 pa0 pb0.
have [||[u v] /= [hu hv] huv] := @annul_div_in_ideal _ p q.
+ by rewrite (@root_size_gt1 _ a) //; apply/rootP.
+ by rewrite (@root_size_gt1 _ b) //; apply/rootP.
by rewrite (huv b) mulrCA divff // mulr1 pa0 pb0 !mulr0 addr0.
Qed.

Lemma annul_div_iotaP (F F' : fieldType) (p q : {poly F}) (a b : F')
  (iota : {rmorphism F -> F'}) : p != 0 -> q != 0 -> b != 0 ->
  (p ^ iota).[a] = 0 -> (q ^ iota).[b] = 0 ->
  ((annul_div p q) ^ iota).[a / b] = 0.
Proof.
move=> p_neq0 q_neq0 b_neq0 pa0 pb0; rewrite /annul_div /= map_resultant;
  do ?by rewrite ?(comp_poly2_eq0, size_XmulC,
    map_poly_eq0, lead_coef_eq0, polyX_eq0).
rewrite /comp_poly /= -!map_poly_comp /=.
have hYmX : 'X * 'Y = ('X * 'Y) ^ (map_poly iota) :> {poly {poly F'}}.
  by rewrite rmorphM /= map_polyC /= !map_polyX.
rewrite -horner_map /= -hYmX -!map_poly_comp /=.
rewrite (eq_map_poly (map_polyC _)) [q ^ _]map_poly_comp /=.
rewrite (@eq_map_poly _ _ _ ((polyC \o polyC) \o iota)); last first.
  by move=> x /=; rewrite map_polyC /= map_polyC.
by rewrite !map_poly_comp /= -/(_ \Po _) annul_divP ?map_poly_eq0.
Qed.

Lemma size_swap_mulX  (R : idomainType) (p : {poly {poly R}}) :
  size (swapXY (p * 'X)) = size (swapXY p).
Proof. by rewrite rmorphM mulrC /= swapXY_X size_Cmul ?polyX_eq0. Qed.

Lemma dvdXp (R : idomainType) (p : {poly R}) : 'X %| p = root p 0.
Proof. by rewrite -dvdp_XsubCl subr0. Qed.

Lemma annul_div_neq0 (F : fieldType) (p q : {poly F}) :
  p != 0 -> q.[0] != 0 -> annul_div p q != 0.
Proof.
move=> p_neq0 q0_neq0; rewrite /annul_div.
rewrite resultant_eq0 -leqNgt leq_eqVlt ltnS leqn0; apply/orP; left.
rewrite -coprimep_def; have [//|] := boolP (coprimep _ _).
case/(Bezout_coprimepPn _ _); do ?by rewrite poly_XmY_eq0.
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
  rewrite swapXY_poly_XmY horner_comp !hornerE horner_map /=.
  rewrite vX0_eq0 mul0r size_poly0 size_poly_eq0 mulf_eq0 polyC_eq0.
  have [/eqP p0_eq0|p0_neq0] := boolP (p.[0] == 0); rewrite (orbT, orbF).
    move=> _; move: (hpq)=> /(f_equal (size \o (eval 0%:P))) /= => /eqP.
    rewrite !{1}rmorphM /= /eval.
    rewrite horner_map /= horner_poly_XmY mul0r comp_poly0r -horner_coef0.
    rewrite p0_eq0 mulr0 size_poly0 eq_sym size_poly_eq0 mulf_eq0 !polyC_eq0.
    rewrite (negPf q0_neq0) orbF -[v]swapXYK swv rmorphM /= hornerM.
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
    rewrite hp /poly_XmY !rmorphM /= !map_polyX comp_polyX.
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
rewrite swapXY_poly_XmY horner_comp !hornerE horner_map /=.
have [-> /eqP|uX0_neq0] := eqVneq (swapXY u).[0] 0.
  rewrite {1}mul0r size_poly0 eq_sym size_poly_eq0 mulf_eq0.
  by rewrite (negPf vX0_neq0) (negPf q_neq0).
have [-> /eqP|p0_neq0] := eqVneq p.[0] 0.
  rewrite {1}mulr0 size_poly0 eq_sym size_poly_eq0 mulf_eq0.
  by rewrite (negPf vX0_neq0) (negPf q_neq0).
rewrite !{1}size_mul ?polyC_eq0 // size_polyC p0_neq0 {1}addn1 /=.
rewrite -[X in (X + _).-1]prednK ?addSn /=; last first.
  by rewrite lt0n size_poly_eq0 vX0_neq0.
move=> huvq; have := leq_size_coef (swapXY u) 0%N.
rewrite -horner_coef0 huvq sizeYE swapXYK=> /leq_ltn_trans /(_ ltn_uq).
by rewrite ltnNge leq_addl.
Qed.

End poly_field_resultant.