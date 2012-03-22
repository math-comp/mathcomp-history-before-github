(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import ssrint polydiv rat.
Require Import mxpoly mxrepresentation vector falgebra algC classfun character.
Require Import fieldext separable galois.

(******************************************************************************)
(* This file should provide the standard results on character integrality,    *)
(* and algebraic integers, including notations and lemmas for reasoning       *)
(* "mod n" in the algebraics, and computing with class sums.                  *)
(*  For now it is a placeholder for the theorem asserting that the degree of  *)
(* an irreducible character of G divides the order of G (Isaacs 3.11).        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section CyclotomicPoly.

Section Ring.

Variable R : ringType.

Definition cyclotomic (z : R) n :=
  \prod_(k < n | coprime k n) ('X - (z ^+ k)%:P).

Lemma cyclotomic_monic z n : cyclotomic z n \is monic.
Proof. exact: monic_prod_XsubC. Qed.

Lemma size_cyclotomic z n : size (cyclotomic z n) = (totient n).+1.
Proof.
rewrite /cyclotomic -big_filter filter_index_enum size_prod_XsubC; congr _.+1.
rewrite -cardE -sum1_card totient_count_coprime big_mkord.
by apply: eq_bigl => k; rewrite coprime_sym.
Qed.

End Ring.

Section Field.

Variables (F : fieldType) (n : nat) (z : F).
Hypothesis prim_z : n.-primitive_root z.
Let n_gt0 := prim_order_gt0 prim_z.

Lemma prod_cyclotomic :
  'X^n - 1 = \prod_(d <- divisors n) cyclotomic (z ^+ (n %/ d)) d.
Proof.
have in_d d: (d %| n)%N -> val (@inord n d) = d by move/dvdn_leq/inordK=> /= ->.
have dv_n k: (n %/ gcdn k n %| n)%N.
  by rewrite -{3}(divnK (dvdn_gcdr k n)) dvdn_mulr.
have [uDn _ inDn] := divisors_correct n_gt0.
have defDn: divisors n = map val (map (@inord n) (divisors n)).
  by rewrite -map_comp map_id_in // => d; rewrite inDn => /in_d.
rewrite defDn big_map big_uniq /=; last first.
  by rewrite -(map_inj_uniq val_inj) -defDn.
pose h (k : 'I_n) : 'I_n.+1 := inord (n %/ gcdn k n).
rewrite -(factor_Xn_sub_1 prim_z) big_mkord.
rewrite (partition_big h (dvdn^~ n)) /= => [|k _]; last by rewrite in_d ?dv_n.
apply: eq_big => d; first by rewrite -(mem_map val_inj) -defDn inDn.
set q := (n %/ d)%N => d_dv_n.
have [q_gt0 d_gt0]: (0 < q /\ 0 < d)%N by apply/andP; rewrite -muln_gt0 divnK.
have fP (k : 'I_d): (q * k < n)%N by rewrite divn_mulAC ?ltn_divLR ?ltn_pmul2l.
rewrite (reindex (fun k => Ordinal (fP k))); last first.
  have f'P (k : 'I_n): (k %/ q < d)%N by rewrite ltn_divLR // mulnC divnK.
  exists (fun k => Ordinal (f'P k)) => [k _ | k /eqnP/=].
    by apply: val_inj; rewrite /= mulKn.
  rewrite in_d // => Dd; apply: val_inj; rewrite /= mulnC divnK // /q -Dd.
  by rewrite divnA ?mulKn ?dvdn_gcdl ?dvdn_gcdr.
apply: eq_big => k; rewrite ?exprM // -val_eqE in_d //=.
rewrite -eqn_mul ?dvdn_gcdr ?gcdn_gt0 ?n_gt0 ?orbT //.
rewrite -[n in gcdn _ n](divnK d_dv_n) -muln_gcdr mulnCA mulnA divnK //.
by rewrite mulnC eqn_mul // divnn n_gt0 eq_sym.
Qed.

End Field.

End CyclotomicPoly.

Section MoreZint.

Definition negz z := if z is Negz _ then true else false.

(* this is mulz_sign_abs *)
Lemma intEsign z : z = (-1) ^+ negz z * `|z|%N%:Z.
Proof. by rewrite mulr_sign; case: z. Qed.

(* this is signr_lt0 *)
Lemma negz_sign (b : bool) : negz ((-1) ^+ b) = b.
Proof. by case: b. Qed.

(* this is mulr_lt0 *)
Lemma negzM z1 z2 :
  negz (z1 * z2) = [&& z1 != 0, z2 != 0 & negz z1 (+) negz z2].
Proof. by case: z1 z2 => [[|m]|m] [[]|]. Qed.

(* this is mulr_sign_lt0 *)
Lemma negzMsign (b : bool) z : 
  negz ((-1) ^+ b * z) = (z != 0) && (b (+) negz z).
Proof. by rewrite negzM signr_eq0 negz_sign. Qed.

(* subsumed by natzP *)
Lemma negzPn z : ~~ negz z -> {n : nat | z = n}.
Proof. by case: z => // n; exists n. Qed.

End MoreZint.

Section ZpolyScale.

Fact int_poly_scale_subproof (p : {poly int}) :
  {d | negz d = negz (lead_coef p)
     & forall a, (`|a| %| `|d|)%N <-> (exists q, p = a *: q)}. 
Proof.
have [-> | nz_p] := eqVneq p 0.
  rewrite lead_coef0; exists 0%N => // a; rewrite dvdn0.
  by split=> // _; exists 0; rewrite scaler0.
have (d : nat): all (dvdn d \o absz) p -> (d <= `|lead_coef p|)%N.
  move/all_nthP=> /= dv_d_p; rewrite dvdn_leq ?absz_gt0 ?lead_coef_eq0 //.
  by rewrite lead_coefE dv_d_p ?prednK // lt0n size_poly_eq0.
case/ex_maxnP=> [|d /(all_nthP 0)/= d_dv_p max_d].
  by exists 1%N; apply/allP=> a _; exact: dvd1n.
pose div_d z := (-1) ^+ negz z * (`|z| %/ d)%N%:Z.
pose r := \poly_(i < size p) div_d p`_i.
have Dp: p = d%:Z *: r.
  apply/polyP=> i; rewrite coefZ coef_poly.
  case: ltnP => [/d_dv_p d_dv_pi | /(nth_default 0)->]; last by rewrite mulr0.
  by rewrite mulrC -mulrA -PoszM divnK // -intEsign.
set a0 := lead_coef p; have nz_a0: a0 != 0 by rewrite lead_coef_eq0.
have d_gt0: (d > 0)%N.
  by rewrite lt0n; apply: contraNneq nz_p => d0; rewrite Dp d0 scale0r.
exists ((-1) ^+ negz a0 * d%:Z) => [|a].
  by rewrite negzMsign addbF -lt0n d_gt0.
rewrite abszMsign; split=> [/dvdnP[d1 Dd] | [q Daq]].
  exists ((-1) ^+ negz a * d1%:Z *: r).
  by rewrite scalerA {1}[a]intEsign mulrAC -!mulrA signrMK -PoszM -Dd.
suffices /eqP->: d == lcmn `|a| d by rewrite dvdn_lcml.
have nz_a: a != 0 by apply: contraNneq nz_p => a_0; rewrite Daq a_0 scale0r.
rewrite eqn_leq dvdn_leq ?dvdn_lcmr ?lcmn_gt0 ?absz_gt0 ?nz_a //=.
rewrite max_d //; apply/(all_nthP 0) => i lt_i_p /=.
by rewrite dvdn_lcm d_dv_p // Daq coefZ abszM dvdn_mulr.
Qed. 

Definition int_poly_scale p := s2val (int_poly_scale_subproof p).

Lemma int_poly_scaleP p a :
  reflect (exists q, p = a *: q) (`|a| %| `|int_poly_scale p|)%N.
Proof.
apply: (equivP idP); rewrite /int_poly_scale.
by case: (int_poly_scale_subproof p).
Qed.

Definition unscale_int_poly p :=
  if p == 0 then 0 else sval (sig_eqW (int_poly_scaleP p _ (dvdnn _))).

Lemma int_polyEscale p : p = int_poly_scale p *: unscale_int_poly p.
Proof.
rewrite /unscale_int_poly.
by case: eqP => [-> | _]; [rewrite scaler0 | case: (sig_eqW _)].
Qed.

Lemma int_poly_scale0 : int_poly_scale 0 = 0.
Proof.
apply/eqP; rewrite -absz_eq0 -dvd0n.
by apply/(int_poly_scaleP 0 0); exists 0; rewrite scale0r.
Qed.

Lemma int_poly_scale_eq0 p : (int_poly_scale p == 0) = (p == 0).
Proof.
apply/idP/idP=> /eqP p0; first by rewrite [p]int_polyEscale p0 scale0r.
by rewrite p0 int_poly_scale0.
Qed.

Lemma unscale_int_poly0 : unscale_int_poly 0 = 0.
Proof. by rewrite /unscale_int_poly eqxx. Qed.

Lemma unscale_int_poly_eq0 p : (unscale_int_poly p == 0) = (p == 0).
Proof.
apply/idP/idP=> /eqP p0; first by rewrite [p]int_polyEscale p0 scaler0.
by rewrite p0 unscale_int_poly0.
Qed.

Lemma negz_int_poly_scale p : negz (int_poly_scale p) = negz (lead_coef p).
Proof. by rewrite /int_poly_scale; case: (int_poly_scale_subproof _). Qed.

Lemma negz_lead_unscale_int_poly p : ~~ negz (lead_coef (unscale_int_poly p)).
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite unscale_int_poly0 lead_coef0.
have:= negz_int_poly_scale p; rewrite {2}[p]int_polyEscale lead_coefZ negzM.
rewrite lead_coef_eq0 int_poly_scale_eq0 unscale_int_poly_eq0 nz_p /=.
by move/(canLR (addKb _)) <-; rewrite addbb.
Qed.

Lemma unscale_int_poly_min p a q :
    p != 0 -> p = a *: q -> 
  {b | negz b = negz (lead_coef q) & q = b *: unscale_int_poly p}.
Proof.
move=> nz_p Dp; set e := negz (lead_coef q).
have /int_poly_scaleP a_dv_p: exists q, p = a *: q by exists q.
pose b := (`|int_poly_scale p| %/ `|a|)%N.
have [nz_a nz_q]: a != 0 /\ q != 0 by apply/norP; rewrite -scale_poly_eq0 -Dp.
exists ((-1) ^+ e * b%:Z).
  rewrite negzMsign addbF -lt0n divn_gt0 ?(absz_gt0, dvdn_leq) //.
  by rewrite int_poly_scale_eq0.
apply/eqP; rewrite -subr_eq0 -(lreg_polyZ_eq0 _ (mulfI nz_a)) scalerBr subr_eq0.
rewrite -Dp scalerA {1}[p]int_polyEscale; apply/eqP; congr (_ *: _).
rewrite [a]intEsign mulrAC -!mulrA -PoszM divnK // mulrA -signr_addb.
rewrite {1}[int_poly_scale p]intEsign; congr (_ ^+ _ * _).
by rewrite negz_int_poly_scale Dp lead_coefZ negzM lead_coef_eq0 nz_a nz_q.
Qed.

Lemma unscale_int_poly_irr p a q :
  p != 0 -> unscale_int_poly p = a *: q -> a = (-1) ^+ negz (lead_coef q).
Proof.
move=> nz_p Dp; have: p = (a * int_poly_scale p) *: q.
  by rewrite mulrC -scalerA -Dp -int_polyEscale.
case/unscale_int_poly_min=> // b <- /eqP.
rewrite Dp -{1}[q]scale1r scalerA -subr_eq0 -scalerBl scale_poly_eq0.
have{Dp} /negPf->: q != 0.
  by move: nz_p; rewrite -unscale_int_poly_eq0 Dp scale_poly_eq0 => /norP[].
by case: a b => [[|[|a]] | [|a]] [[|[|b]] | [|b]] //; rewrite mulr0.
Qed.

Lemma unscale_int_poly_id p :
  unscale_int_poly (unscale_int_poly p) = unscale_int_poly p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite !unscale_int_poly0.
rewrite {2}[unscale_int_poly p]int_polyEscale.
rewrite [int_poly_scale _](unscale_int_poly_irr nz_p (int_polyEscale _)).
by rewrite (negPf (negz_lead_unscale_int_poly _)) scale1r.
Qed.

Lemma unscale_int_polyZ a p :
  a != 0 -> unscale_int_poly (a *: p) = unscale_int_poly p.
Proof.
have [-> | nz_p nz_a] := eqVneq p 0; first by rewrite scaler0.
have: a *: p = (a * int_poly_scale p) *: unscale_int_poly p.
  by rewrite -scalerA -int_polyEscale.
case/unscale_int_poly_min=> [|b _ Dp].
  by rewrite scale_poly_eq0; exact/norP.
rewrite Dp (unscale_int_poly_irr nz_p Dp).
by rewrite (negPf (negz_lead_unscale_int_poly _)) scale1r.
Qed.

Lemma unscale_int_polyM p1 p2 :
  unscale_int_poly (p1 * p2) = unscale_int_poly p1 * unscale_int_poly p2.
Proof.
have [p12_0 | nz_p12] := eqVneq (p1 * p2) 0.
  rewrite p12_0; move/eqP: p12_0; rewrite mulf_eq0.
  by case/pred2P=> ->; rewrite !unscale_int_poly0 (mul0r, mulr0).
have [nz_p1 nz_p2]: p1 != 0 /\ p2 != 0 by apply/norP; rewrite -mulf_eq0.
rewrite {1}[p1]int_polyEscale {1}[p2]int_polyEscale -scalerAl -scalerAr.
rewrite scalerA unscale_int_polyZ ?mulf_neq0 ?int_poly_scale_eq0 //.
set p := _ * _; rewrite {2}[p]int_polyEscale; set d := int_poly_scale p.
have [||d1] := ltngtP `|d|%N 1%N; last 1 first.
- rewrite [d]intEsign d1 mulr1 negz_int_poly_scale lead_coefM.
  rewrite negzM !lead_coef_eq0 !unscale_int_poly_eq0 nz_p1 nz_p2 /=.
  by rewrite !(negPf (negz_lead_unscale_int_poly _)) scale1r.
- by rewrite ltnNge absz_gt0 int_poly_scale_eq0 mulf_neq0 ?unscale_int_poly_eq0.
case/pdivP=> r r_pr r_dv_d; pose to_r : int -> 'F_r := *~%R 1.
have nz_unscale_r q: q != 0 -> map_poly to_r (unscale_int_poly q) != 0.
  set q1 := unscale_int_poly q => nz_q.
  apply: contraTneq (prime_gt1 r_pr) => r_dv_q.
  pose q2 := \poly_(i < size q1) ((-1) ^+ negz q1`_i * Posz (`|q1`_i| %/ r)).
  have: q1 = r%:Z *: q2.
    apply/polyP=> i; rewrite coefZ -[q1]coefK !coef_poly.
    case: ifP => _; rewrite ?mulr0 // mulrC -mulrA -PoszM divnK -?intEsign //.
    have /polyP/(_ i)/eqP := r_dv_q.
    rewrite coef_map /= coef0 {1}[q1`_i]intEsign rmorphM rmorph_sign.
    by rewrite mulf_eq0 signr_eq0 /= -val_eqE /= val_Fp_nat.
  by move/(unscale_int_poly_irr nz_q); case: (negz _) => // [[->]].
suffices{nz_unscale_r} /idPn[]: map_poly to_r p == 0.
  by rewrite rmorphM mulf_neq0 ?nz_unscale_r.
rewrite [p]int_polyEscale -/d [d]intEsign mulrC -scalerA map_polyZ /=.
by rewrite scale_poly_eq0 -val_eqE /= val_Fp_nat ?(eqnP r_dv_d).
Qed.

Lemma size_unscale_int_poly p : size (unscale_int_poly p) = size p.
Proof.
have [-> | ] := eqVneq p 0; first by rewrite unscale_int_poly0.
by rewrite {1 3}[p]int_polyEscale scale_poly_eq0 => /norP[/size_scale-> _].
Qed.

Lemma int_scale_monic p : p \is monic -> int_poly_scale p = 1.
Proof.
move/monicP=> lead_p_1; rewrite [_ p]intEsign negz_int_poly_scale lead_p_1.
have /esym/eqP := congr1 (absz \o lead_coef) (int_polyEscale p).
by rewrite /= lead_p_1 lead_coefZ abszM muln_eq1 => /andP[/eqP-> _].
Qed.

Lemma unscale_int_monic p : p \in monic -> unscale_int_poly p = p.
Proof. by move=> ?; rewrite {2}[p]int_polyEscale int_scale_monic ?scale1r. Qed.

Lemma dvdpP_int p q : p %| q -> {r | q = unscale_int_poly p * r}.
Proof.
case/ID.dvdpP/sig2_eqW=> [[c r] /= nz_c Dpr].
exists (int_poly_scale q *: unscale_int_poly r); rewrite -scalerAr.
by rewrite -unscale_int_polyM mulrC -Dpr unscale_int_polyZ // -int_polyEscale.
Qed.

Local Notation pZtoQ := (map_poly (intr : int -> rat)).

Lemma size_rat_int_poly p : size (pZtoQ p) = size p.
Proof. by apply: size_map_inj_poly; first exact: intr_inj. Qed.

Lemma rat_poly_scale (p : {poly rat}) :
  {q : {poly int} & {a | a != 0 & p = a%:~R^-1 *: pZtoQ q}}.
Proof.
pose a := \prod_(i < size p) denq p`_i.
have nz_a: a != 0 by apply/prodf_neq0=> i _; exact: denq_neq0.
exists (map_poly numq (a%:~R *: p)), a => //.
apply: canRL (scalerK _) _; rewrite ?intr_eq0 //.
apply/polyP=> i; rewrite !(coefZ, coef_map_id0) // numqK // Qint_def mulrC.
have [ltip | /(nth_default 0)->] := ltnP i (size p); last by rewrite mul0r.
by rewrite [a](bigD1 (Ordinal ltip)) // rmorphM mulrA -numqE -rmorphM denq_int.
Qed.

Lemma dvdp_rat_int p q : (pZtoQ p %| pZtoQ q) = (p %| q).
Proof.
apply/dvdpP/ID.dvdpP=> [[/= r1 Dq] | [[/= a r] nz_a Dq]]; last first.
  exists (a%:~R^-1 *: pZtoQ r); rewrite -scalerAl -rmorphM -Dq.
  by rewrite -{2}[a]intz scaler_int rmorphMz -scaler_int scalerK ?intr_eq0.
have [r [a nz_a Dr1]] := rat_poly_scale r1; exists (a, r) => //=.
apply: (map_inj_poly _ _ : injective pZtoQ) => //; first exact: intr_inj.
rewrite -[a]intz scaler_int rmorphMz -scaler_int /= Dq Dr1.
by rewrite -scalerAl -rmorphM scalerKV ?intr_eq0.
Qed.

Lemma dvdpP_rat_int p q :
    p %| pZtoQ q ->
  {p1 : {poly int} & {a | a != 0 & p = a *: pZtoQ p1} & {r | q = p1 * r}}.
Proof.
have{p} [p [a nz_a ->]] := rat_poly_scale p.
rewrite dvdp_scalel ?invr_eq0 ?intr_eq0 // dvdp_rat_int => dv_p_q.
exists (unscale_int_poly p); last exact: dvdpP_int.
have [-> | nz_p] := eqVneq p 0.
  by exists 1; rewrite ?oner_eq0 // unscale_int_poly0 map_poly0 !scaler0.
exists ((int_poly_scale p)%:~R / a%:~R).
  by rewrite mulf_neq0 ?invr_eq0 ?intr_eq0 ?int_poly_scale_eq0.
by rewrite mulrC -scalerA -map_polyZ -int_polyEscale.
Qed.

End ZpolyScale.

Section AlgCRect.
(* Imaginary numbers and rectangular coordinates. This is proof-of-concept    *)
(* only, and not currently used in the rest of the formalization (it was part *)
(* of a failed early automorphism construction attempt).                      *)
Definition algCi : algC := sqrtC (- 1).
Definition alg_Re x := (x + x^*) / 2%:R.
Definition alg_Im x := (x - x^*) / (algCi *+ 2).

Lemma sqr_algCi : algCi ^+ 2 = -1. Proof. exact: sqrtCK. Qed.

Lemma algCi_nonReal : ~~ isRealC algCi.
Proof.
apply: contraFN (ltC_geF sposC1) => /real_normCK norm_i.
by rewrite -posC_opp -sqr_algCi -norm_i sqrtCK posC_pconj.
Qed.

Lemma algCi_neq0 : algCi != 0.
Proof. by apply: contraNneq algCi_nonReal => ->; exact: isIntC_Real. Qed.

Lemma normCi : `|algCi| = 1.
Proof.
apply/eqP; rewrite -(@posC_unit_exp _ 1) ?posC_norm // -normC_exp sqr_algCi.
by rewrite normC_opp normC1.
Qed.

Lemma conjCi : algCi^* = - algCi.
Proof.
have: root (\prod_(z <- [:: algCi; -algCi]) ('X - z%:P)) algCi^*.
  rewrite big_cons big_seq1 raddfN opprK -subr_sqr -rmorphX sqr_algCi.
  by rewrite /root !hornerE -expr2 -rmorphX sqr_algCi rmorphN rmorph1 subrr.
by rewrite root_prod_XsubC !inE [_ == _](negPf algCi_nonReal) => /eqP.
Qed.

Lemma invCi : algCi^-1 = - algCi.
Proof. by rewrite invC_norm normCi conjCi expr1n invr1 mul1r. Qed.

Lemma algCrect x : x = alg_Re x + algCi * alg_Im x.
Proof. 
rewrite mulrCA -mulr_natr invfM mulVKf ?algCi_neq0 // -mulrDl.
by rewrite addrCA !addrA addrK -mulr2n -mulr_natr mulfK -?neq0N_neqC.
Qed.

Lemma alg_Re_Real x : isRealC (alg_Re x).
Proof. by rewrite /isRealC fmorph_div rmorph_nat rmorphD conjCK addrC. Qed.

Lemma alg_Im_Real x : isRealC (alg_Im x).
Proof.
rewrite /isRealC fmorph_div rmorphMn conjCi mulNrn invrN mulrN -mulNr.
by rewrite rmorphB conjCK opprB.
Qed.

Lemma isRealC_conj x : isRealC x -> x^* = x. Proof. by move/eqP. Qed.

Lemma alg_Re_rect x y : isRealC x -> isRealC y -> alg_Re (x + algCi * y) = x.
Proof.
move=> Rx Ry; rewrite /alg_Re rmorphD addrCA !addrA rmorphM conjCi mulNr.
by rewrite !isRealC_conj // addrK -mulr2n -mulr_natr mulfK -?neq0N_neqC.
Qed.

Lemma alg_Im_rect x y : isRealC x -> isRealC y -> alg_Im (x + algCi * y) = y.
Proof.
move=> Rx Ry; rewrite /alg_Im rmorphD opprD addrAC -!addrA rmorphM conjCi.
rewrite mulNr opprK !isRealC_conj // addNKr -(mulrC y) -mulr2n -mulrnAr.
by rewrite mulfK // -mulr_natr mulf_neq0 ?algCi_neq0 -?neq0N_neqC.
Qed.

End AlgCRect.

Section AlgCorder.
(* Link to numFieldType, used (for now) only to get intr injectivity and      *)
(* ratr morphism properties. Note that since the head symbol of algC : Type  *)
(* is in fact GRing.ClosedField.sort, the structures below are in fact        *)
(* incompatible with some the canonical ones declared by ssrnum.          *)
Import ssrnum.

Fact algC_numRingMixin : Num.mixin_of algC.
Proof.
apply: (@NumMixin _ leC ltC normC) => //.
+ exact: normC_add.
+ by move=> x y x_gt0 y_gt0; rewrite sposC_addl // ltCW.
+ by move=> x /eqP; rewrite normC_eq0 => /eqP.
+ move=> x y x_ge0 y_ge0; apply/orP.
  rewrite -leC_sub -[leC y x]leC_sub -opprB posC_opp.
  by apply: leC_real_total; rewrite rmorphB !posC_conjK.
+ exact: normC_mul.
+ move=> x y; rewrite -leC_sub; move: (_ - _) => z; apply/idP/eqP.
    by move=> /normC_pos.
  by move<-; rewrite posC_norm.
Qed.

Definition algC_numIdomainType := NumIdomainType algC algC_numRingMixin.
Definition algC_numFieldType := NumFieldType algC algC_numRingMixin.

End AlgCorder.

Canonical algC_numIdomainType.
Canonical algC_numFieldType.

Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).

Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).

Local Hint Resolve (@intr_inj algC_numIdomainType).
Local Notation QtoC_M := (ratr_rmorphism algC_numFieldType).

(* More axiom reconstruction... *)
Lemma algC_archimedean x : 0 <= x -> {n | n%:R <= x & x < n.+1%:R}.
Proof.
have trichotomy01 y: 0 <= y -> 1 <= y \/ y <= 1.
  move=> y_ge0; rewrite -leC_sub -(leC_sub y) -opprB posC_opp.
  by apply/realC_leP; rewrite /isRealC rmorphB rmorph1 posC_conjK.
move=> pos_x; suffices /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R.
  exists n => //; case Dn: n => // [n1]; rewrite -Dn.
  have /trichotomy01/orP: 0 <= x / n%:R by rewrite posC_div ?posC_nat.
  have n_gt0: 0 < n%:R by [rewrite -(ltn_ltC 0) Dn].
  have [nz_n _] := andP n_gt0.
  rewrite -(leC_pmul2r _ _ n_gt0) -(leC_pmul2r _ 1 n_gt0) divfK // mul1r.
  case/orP=> //; rewrite leC_eqVlt.
  case/predU1P=> [-> | ]; first exact: leC_refl.
  by rewrite Dn => /min_n; rewrite Dn ltnn.
suffices [n x_le_n]: exists n, x <= n%:R.
  by exists n; rewrite (leC_ltC_trans x_le_n) -?ltn_ltC.
have [x_ge1 | x_le1] := trichotomy01 x pos_x; last by exists 1%N.
have [p nz_p px0] := algC_algebraic x; pose n := (size p).-2.
have Dn: n.+2 = size p.
  rewrite /n -subn2 -addn2 subnK // ltnNge.
  apply: contra nz_p => /size1_polyC Dp; rewrite Dp polyC_eq0.
  by rewrite Dp /root map_polyC hornerC intr_eq0 in px0.
have xk_gt0 k: 0 < x ^+ k by rewrite sposC_exp // (ltC_leC_trans sposC1).  
exists (\sum_(i < n.+1) `|(p`_i)%R|)%N.
apply: leC_trans (_ : x <= `|lead_coef p|%:R * x) _.
  rewrite -{1}[x]mul1r leC_pmul2r ?(xk_gt0 1%N) // -(leq_leC 1) lt0n.
  by rewrite absz_eq0 lead_coef_eq0.
rewrite -[_ * x]subr0 -(leC_pmul2r _ _ (xk_gt0 n)) mulrBl mul0r -mulrA.
rewrite -exprS -(mulr0 ((-1) ^+ negz (lead_coef p))) -(eqP px0) horner_coef.
rewrite size_map_inj_poly // lead_coefE -Dn big_ord_recr coef_map.
move: p`_n.+1 => a /=; rewrite addrC {2}[a]intEsign mulrDr.
rewrite !rmorphM rmorph_sign -mulrA signrMK opprD addrNK mulr_sumr.
rewrite -leC_sub opprK natr_sum mulr_suml -big_split /= posC_sum // => i _.
rewrite coef_map {2}[p`_i]intEsign /= rmorphM rmorph_sign !mulrA -signr_addb.
rewrite -mulrA mulrCA -mulrDr posC_mul ?posC_nat // mulr_sign.
case: ifP => _; last by rewrite posC_add ?ltCW.
rewrite leC_sub -{2}(subnK (leq_ord i)) -[x ^+ i]mul1r exprD.
by case: (n - i)%N => [|k]; rewrite ?leC_refl // leC_pmul2r // leC1exp.
Qed.

(* Countability. *)
Lemma algC_countMixin : Countable.mixin_of algC.
Proof.
pose code x :=
  let p := s2val (sig2_eqW (algC_algebraic x)) in
  (p : seq int, index x (sval (closed_field_poly_normal (pZtoC p)))).
pose decode pi :=
  (sval (closed_field_poly_normal (Poly (map ZtoC pi.1))))`_(pi.2).
apply: CanCountMixin (code) (decode) _ => x; rewrite {}/decode {code}/=.
rewrite -map_polyE; case: (sig2_eqW _) => p /= nz_p px0.
case: (closed_field_poly_normal _) => r /= Dp; apply: nth_index.
have nz_a: lead_coef (pZtoC p) != 0.
  by rewrite lead_coef_map_inj // intr_eq0 lead_coef_eq0.
by rewrite -root_prod_XsubC -(rootZ _ _ nz_a) -Dp.
Qed.

(* This should be file-local, as it makes algC into THE canonical countable *)
(* closedFieldType.                                                         *)
Canonical algC_countType := CountType algC algC_countMixin.

(* Integer subring; this should replace isIntC / getIntC. *)
Lemma isIntC_int z : isIntC z%:~R.
Proof.
by rewrite [z]intEsign rmorphM rmorph_sign isIntC_mul_sign isIntC_nat.
Qed.

Definition getCint z := (-1) ^+ (z < 0)%R * (getNatC `|z|)%:Z.
Local Notation CtoZ := getCint.

Lemma getCintK z : isIntC z -> {for z, cancel CtoZ ZtoC}.
Proof.
rewrite /{for z, _} /= => Zz; rewrite rmorphM rmorph_sign /= -pmulrn.
by rewrite -(eqP (normIntC_Nat Zz)) -isIntC_signE.
Qed.

Lemma CintrK : cancel ZtoC CtoZ. 
Proof.
move=> z; rewrite [z]intEsign rmorphM rmorph_sign /= /getCint.
rewrite normC_mul_sign normC_nat getNatC_nat; congr (_ ^+ _ * _).
case: z => n; first by rewrite mul1r leC_gtF ?posC_nat.
by rewrite -sposC_opp mulN1r opprK -(ltn_ltC 0).
Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  isNatC x -> x \in kS.
Proof. by case/isNatCP=> n ->; apply: rpred_nat. Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  isIntC x -> x \in kS.
Proof. by move/getCintK <-; apply: rpred_int. Qed.

Lemma getCint0 : CtoZ 0 = 0. Proof. exact: (CintrK 0). Qed.
Hint Resolve getCint0.

Lemma getCintpK (p : {poly algC}) :
  all isIntC p -> pZtoC (map_poly CtoZ p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/getCintK// | _]; rewrite getCint0.
Qed.

Lemma getCintpP (p : {poly algC}) : all isIntC p -> {q | p = pZtoC q}.
Proof. by exists (map_poly CtoZ p); rewrite getCintpK. Qed.

(* Reconstructed rational subring. *)
(* Note that this proof is tweaked so that it depends only on the fact that *)
(* QtoC is a field embedding, and not on the order structure assumed for C. *)
(* Thus, it could be used in (and moved to) the construction of C.          *)
Fact getCrat_subproof : {CtoQ | cancel QtoC CtoQ}.
Proof.
have QtoCinj: injective QtoC by exact: fmorph_inj.
have ZtoQinj: injective ZtoQ by exact: intr_inj.
have defZtoC: ZtoC =1 QtoC \o ZtoQ by move=> m; rewrite /= rmorph_int.
suffices CtoQ x: {xa : seq rat | forall a, x = QtoC a -> a \in xa}.
  exists (fun x => let: exist xa _ := CtoQ x in xa`_(index x (map QtoC xa))).
  move=> a /=; case: (CtoQ _) => xa /= /(_ a (erefl _)) xa_a; apply: QtoCinj.
  by rewrite -(nth_map _ 0) ?nth_index -?(size_map QtoC) ?index_mem ?map_f.
have [-> | nz_x] := eqVneq x 0.
  by exists [:: 0] => a; rewrite inE -(inj_eq QtoCinj) rmorph0 => <-.
have /sig2_eqW[p nz_p px0] := algC_algebraic x.
without loss{nz_x} nz_p0: p nz_p px0 / p`_0 != 0.
  move=> IH; elim/poly_ind: p nz_p => [/eqP// | p a IHp nz_p] in px0.
  have [a0 | nz_a] := eqVneq a 0; last first.
    by apply: IH nz_p px0 _; rewrite coefD coefC coefMX add0r.
  rewrite a0 addr0 mulrC mulf_eq0 -size_poly_eq0 size_polyX in nz_p px0.
  apply: IHp nz_p _; rewrite rmorphM rootM /= map_polyX in px0.
  by rewrite {1}/root hornerX (negPf nz_x) in px0.
pose p_n := lead_coef p; pose q e m : rat := (-1) ^+ e * m%:R / `|p_n|%:R.
exists [seq q e m | e <- iota 0 2, m <- divisors `|p_n * p`_0|] => a Dx.
rewrite {x}Dx (eq_map_poly defZtoC) map_poly_comp fmorph_root /root in px0.
have [n Dn]: {n | size p = n.+2}.
  exists (size p - 2)%N; rewrite -addn2 subnK // ltnNge. 
  apply: contra nz_p => /size1_polyC Dp; rewrite Dp polyC_eq0.
  by rewrite Dp map_polyC hornerC intr_eq0 in px0.
pose qn (c : int) m := c * (m ^ n.+1)%N.
pose Eqn (c0 c1 c2 : int) d m := qn c0 d + qn c1 m = c2 * d * m.
have Eqn_div c1 c2 d m c0: coprime m d -> Eqn c0 c1 c2 d m -> (m %| `|c0|)%N.
  move=> co_m_d /(canRL (addrK _))/(congr1 (dvdn m \o absz))/=.
  rewrite abszM mulnC Gauss_dvdr ?coprime_expr // => ->.
  by rewrite -mulNr expnSr PoszM mulrA -mulrDl abszM dvdn_mull.
pose m := numq a; pose d := `|denq a|%N.
have co_md: coprime `|m| d by exact: coprime_num_den.
have Dd: denq a = d by rewrite /d; case: (denq a) (denq_gt0 a).
have{px0} [c Dc1 Emd]: {c | `|c.1|%N = `|p_n|%N & Eqn p`_0 c.1 c.2 d `|m|%N}.
  pose e : int := (-1) ^+ negz m.
  pose r := \sum_(i < n) p`_i.+1 * m ^+ i * (d ^ (n - i.+1))%N.
  exists (e ^+ n.+1 * p_n, - (r * e)); first by rewrite -exprM abszMsign.
  apply/eqP; rewrite !mulNr -addr_eq0 (mulrAC r) -!mulrA -intEsign addrAC.
  apply/eqP; transitivity (\sum_(i < n.+2) p`_i * m ^+ i * (d ^ (n.+1 - i))%N).
    rewrite big_ord_recr big_ord_recl subnn !mulr1; congr (_ + _ + _).
      rewrite mulr_suml; apply: eq_bigr => i _; rewrite -!mulrA; congr (_ * _).
      by rewrite /= mulrC -!mulrA -exprS mulrA -PoszM -expnSr mulrC -subSn.
    rewrite /qn /p_n lead_coefE Dn mulrAC mulrC; congr (_ * _).
    rewrite -[Posz (_ ^ _)]intz -pmulrn natrX pmulrn intz.
    by rewrite -exprMn -intEsign.
  apply: (ZtoQinj); rewrite rmorph0 -(mul0r (ZtoQ (d ^ n.+1)%N)) -(eqP px0).
  rewrite rmorph_sum horner_coef (size_map_inj_poly ZtoQinj) // Dn mulr_suml.
  apply: eq_bigr => i _; rewrite coef_map !rmorphM !rmorphX /= numqE Dd.
  by rewrite -!pmulrn !natrX exprMn -!mulrA -exprD subnKC ?leq_ord.
have{Dc1} /dvdnP[d1 Dp_n]: (d %| `|p_n|)%N.
  rewrite -Dc1 (Eqn_div p`_0 c.2 `|m|%N) 1?coprime_sym //.
  by rewrite /Eqn mulrAC addrC //.
have [d1_gt0 _]: (0 < d1 /\ 0 < d)%N.
  by apply/andP; rewrite -muln_gt0 -Dp_n absz_gt0 lead_coef_eq0. 
have dv_md1_p0n: (`|m| * d1 %| `|p_n| * `|(p`_0)%R|)%N.
  by rewrite Dp_n mulnC -mulnA dvdn_pmul2l ?dvdn_mull // (Eqn_div c.1 c.2 d).
apply/allpairsP; exists (negz m : nat, `|m| * d1)%N.
rewrite mem_iota ltnS leq_b1; split=> //.
  by rewrite abszM -dvdn_divisors // muln_gt0 !absz_gt0 lead_coef_eq0 nz_p.
rewrite /q Dp_n !natrM invfM !mulrA !pmulrn -rmorphMsign -intEsign /=.
by rewrite -Dd mulfK ?divq_num_den // intr_eq0 -lt0n.
Qed.

Definition getCrat := sval getCrat_subproof.
Local Notation CtoQ := getCrat.
Definition Crat : pred algC := (fun x => x == QtoC (CtoQ x)).
Fact Crat_key : pred_key Crat. Proof. by []. Qed.
Canonical Crat_keyed := KeyedPred Crat_key.

Lemma CratrK : cancel QtoC CtoQ.
Proof. by rewrite /getCrat; case: getCrat_subproof. Qed.

Lemma getCratK : {in Crat, cancel CtoQ QtoC}.
Proof. by move=> x /eqP. Qed.

Lemma ratr_Crat y : QtoC y \in Crat.
Proof. by rewrite unfold_in /Crat CratrK. Qed.

Lemma CratP x : reflect (exists a, x = QtoC a) (x \in Crat).
Proof.
by apply: (iffP eqP) => [-> | [a ->]]; [exists (CtoQ x) | rewrite CratrK].
Qed.

Lemma Crat0 : 0 \in Crat. Proof. by apply/CratP; exists 0; rewrite rmorph0. Qed.
Lemma Crat1 : 1 \in Crat. Proof. by apply/CratP; exists 1; rewrite rmorph1. Qed.
Hint Resolve Crat0 Crat1.

Fact Crat_divring_closed : divring_closed Crat.
Proof.
split=> // _ _ /CratP[x ->] /CratP[y ->].
  by rewrite -rmorphB ratr_Crat.
by rewrite -fmorph_div ratr_Crat.
Qed.
Canonical Crat_opprPred := OpprPred Crat_divring_closed.
Canonical Crat_addrPred := AddrPred Crat_divring_closed.
Canonical Crat_mulrPred := MulrPred Crat_divring_closed.
Canonical Crat_zmodPred := ZmodPred Crat_divring_closed.
Canonical Crat_semiringPred := SemiringPred Crat_divring_closed.
Canonical Crat_smulrPred := SmulrPred Crat_divring_closed.
Canonical Crat_divrPred := DivrPred Crat_divring_closed.
Canonical Crat_subringPred := SubringPred Crat_divring_closed.
Canonical Crat_sdivrPred := SdivrPred Crat_divring_closed.
Canonical Crat_divringPred := DivringPred Crat_divring_closed.

Lemma rpred_Crat S (ringS : divringPred S) (kS : keyed_pred ringS) :
  {subset Crat <= kS}.
Proof. by move=> _ /CratP[a ->]; apply: rpred_rat. Qed.

Lemma CratV x : (x^-1 \in Crat) = (x \in Crat).
Proof. exact: rpredV. Qed.

Lemma CratXz m : {in Crat, forall x, x ^ m \in Crat}.
Proof. exact: rpredXint. Qed.

Lemma Crat_div : {in Crat &, forall x y, x / y \in Crat}.
Proof. exact: rpred_div. Qed.

Lemma conj_Crat z : z \in Crat -> z^* = z.
Proof. by move/getCratK <-; rewrite fmorph_div !rmorph_int. Qed.

Lemma Creal_Rat z : z \in Crat -> isRealC z.
Proof. by move/conj_Crat/eqP. Qed.

Lemma Cint_ratr a : isIntC (QtoC a) = (a \in Qint).
Proof.
apply/idP/idP=> [Za | /numqK <-]; last by rewrite rmorph_int isIntC_int.
apply/QintP; exists (CtoZ (QtoC a)); apply: (can_inj CratrK).
by rewrite rmorph_int getCintK.
Qed.

(* Minimal polynomial. *)

Fact minCpoly_subproof (x : algC) :
  {p | p \is monic & forall q, root (pQtoC q) x = (p %| q)}.
Proof.
have /sig2_eqW[p0 nz_p0 p0x] := algC_algebraic x.
have [r Dp0] := closed_field_poly_normal (pZtoC p0).
do [rewrite lead_coef_map_inj //; set d0 := _%:~R] in Dp0.
have{nz_p0} nz_d0: d0 != 0 by rewrite intr_eq0 lead_coef_eq0.
have r_x: x \in r by rewrite Dp0 rootZ // root_prod_XsubC in p0x.
pose p_ (I : {set 'I_(size r)}) := \prod_(i <- enum I) ('X - (r`_i)%:P).
pose Qpx I := root (p_ I) x && all (mem Crat) (p_ I).
have{d0 p0 nz_d0 p0x Dp0} /minset_exists[I /minsetP[]]: Qpx setT.
  rewrite /Qpx; have ->: p_ setT = d0^-1 *: intrp p0.
     rewrite Dp0 scalerK // (big_nth 0) big_mkord /p_ big_filter /=.
     by apply: eq_bigl => i; rewrite inE.
   rewrite rootZ ?invr_eq0 // p0x; apply/(all_nthP 0)=> i _ /=.
   by rewrite coefZ mulrC coef_map Crat_div ?rpred_int.
case/andP=> pIx QpI minI _; pose p := map_poly CtoQ (p_ I).
have DpI: p_ I = pQtoC p.
  rewrite -[p_ I]coefK; apply/polyP=> i; rewrite -map_poly_comp !coef_poly.
  by case: ifP => //= lti_pI; rewrite getCratK //; exact: (all_nthP 0 QpI).
exists p; first by rewrite -(map_monic QtoC_M) -DpI monic_prod_XsubC.
move=> q; rewrite -(dvdp_map QtoC_M) -DpI.
apply/idP/idP=> [qx0 | /dvdpP[{q} q ->]]; last by rewrite rootM pIx orbT.
pose q1 := gcdp p q; have /dvdp_prod_XsubC[m Dq1]: pQtoC q1 %| p_ I.
  by rewrite gcdp_map DpI dvdp_gcdl.
pose B := [set i \in mask m (enum I)].
have{Dq1} Dq1: pQtoC q1 %= p_ B.
  congr (_ %= _): Dq1; apply: eq_big_perm.
  by rewrite uniq_perm_eq ?mask_uniq ?enum_uniq // => i; rewrite mem_enum inE.
rewrite -(minI B); first by rewrite -(eqp_dvdl _ Dq1) gcdp_map dvdp_gcdr.
  rewrite /Qpx -(eqp_root Dq1) gcdp_map root_gcd qx0 -DpI pIx.
  have{Dq1} /eqpP[[d1 d2] /= /andP[nz_d1 nz_d2] Dq1] := Dq1.
  rewrite -[p_ B](scalerK nz_d2) -Dq1 scalerA mulrC.
  have ->: d1 / d2 = (QtoC (lead_coef q1))^-1.
    have:= congr1 lead_coef Dq1; rewrite !lead_coefZ lead_coef_map.
    rewrite (monicP (monic_prod_XsubC _ _ _)) mulr1 => <-.
    by rewrite invfM mulVKf.
  apply/(all_nthP 0)=> i _; rewrite coefZ coef_map mulrC /=.
  by rewrite Crat_div ?ratr_Crat.
by apply/subsetP=> i; rewrite inE => /mem_mask; rewrite mem_enum.
Qed.

Definition minCpoly x : {poly algC} :=
  locked (pQtoC (s2val (minCpoly_subproof x))).

Lemma minCpolyP x :
   {p | minCpoly x = pQtoC p /\ p \is monic
      & forall q, root (pQtoC q) x = (p %| q)}.
Proof. by unlock minCpoly; case: (minCpoly_subproof x) => p /=; exists p. Qed.

Lemma minCpoly_monic x : minCpoly x \is monic.
Proof. by have [p [-> mon_p] _] := minCpolyP x; rewrite map_monic. Qed.

Lemma minCpoly_eq0 x : (minCpoly x == 0) = false.
Proof. exact/negbTE/monic_neq0/minCpoly_monic. Qed.

Lemma root_minCpoly x : root (minCpoly x) x.
Proof. by have [p [-> _] ->] := minCpolyP x. Qed.

Lemma size_minCpoly x : (1 < size (minCpoly x))%N.
Proof.
apply: contraFT (minCpoly_eq0 x); rewrite -leqNgt => /size1_polyC Dp.
by have /eqP := root_minCpoly x; rewrite Dp hornerC => ->.
Qed.

(* Number fields and rational spans. *)
Lemma algC_PET (s : seq algC) :
  {z | exists a : nat ^ size s, z = \sum_(i < size s) s`_i *+ a i
     & exists ps, s = [seq (pQtoC p).[z] | p <- ps]}.
Proof.
elim: s => [|x s [z /sig_eqW[a Dz] /sig_eqW[ps Ds]]].
  by exists 0; [exists [ffun _ => 2]; rewrite big_ord0 | exists nil].
have r_exists (y : algC): {r | r != 0 & root (pQtoC r) y}.
  have [r [_ mon_r] dv_r] := minCpolyP y.
  by exists r; rewrite ?monic_neq0 ?dv_r.
suffices /sig_eqW[[n [|px [|pz []]]]// [Dpx Dpz]]:
  exists np, let zn := x *+ np.1 + z in
    [:: x; z] = [seq (pQtoC p).[zn] | p <- np.2].
- exists (x *+ n + z).
    exists [ffun i => oapp a n (unlift ord0 i)].
    rewrite /= big_ord_recl ffunE unlift_none Dz; congr (_ + _).
    by apply: eq_bigr => i _; rewrite ffunE liftK.
  exists (px :: [seq p \Po pz | p <- ps]); rewrite /= -Dpx; congr (_ :: _).
  rewrite -map_comp Ds; apply: eq_map => p /=.
  by rewrite map_comp_poly horner_comp -Dpz.
have [rx nz_rx rx0] := r_exists x.
have [rz nz_rz rz0] := r_exists (- z).
have char0_Q: [char rat] =i pred0 by exact: ssrnum.Num.char_num.
have [n [[pz Dpz] [px Dpx]]] := PET_char0 nz_rz rz0 nz_rx rx0 char0_Q.
by exists (n, [:: px; - pz]); rewrite /= !raddfN hornerN -[z]opprK Dpz Dpx.
Qed.

Canonical subfx_unitAlgType (F L : fieldType) iota (z : L) p :=
  Eval hnf in [unitAlgType F of subFExtend iota z p].

Lemma num_field_exists (s : seq algC) :
  {Qs : fieldExtType rat & {QsC : {rmorphism Qs -> algC}
   & {s1 : seq Qs | map QsC s1 = s & genField 1 s1 = fullv}}}.
Proof.
have [z /sig_eqW[a Dz] /sig_eqW[ps Ds]] := algC_PET s.
suffices [Qs [QsC [z1 z1C z1gen]]]:
  {Qs : fieldExtType rat & {QsC : {rmorphism Qs -> algC} &
     {z1 : Qs | QsC z1 = z & forall x, exists p, fieldExt_horner z1 p = x}}}.
- set inQs := fieldExt_horner z1 in z1gen *; pose s1 := map inQs ps.
  have inQsK p: QsC (inQs p) = (pQtoC p).[z].
    rewrite /= -horner_map z1C -map_poly_comp; congr _.[z].
    apply: eq_map_poly => b /=; apply: canRL (mulfK _) _.
      by rewrite intr_eq0 denq_eq0.
    rewrite /= mulrzr -rmorphMz scalerMzl -{1}[b]divq_num_den -mulrzr.
    by rewrite divfK ?intr_eq0 ?denq_eq0 // scaler_int rmorph_int.
  exists Qs, QsC, s1; first by rewrite -map_comp Ds (eq_map inQsK).
  have sz_ps: size ps = size s by rewrite Ds size_map.
  apply/vspaceP=> x; rewrite memvf; have [p {x}<-] := z1gen x.
  elim/poly_ind: p => [|p b ApQs]; first by rewrite /inQs rmorph0 mem0v.
  rewrite /inQs rmorphD rmorphM /= fieldExt_hornerX fieldExt_hornerC -/inQs /=.
  suffices ->: z1 = \sum_(i < size s) s1`_i *+ a i.
    rewrite memvD ?memvZ ?mem1v ?memv_mul ?memv_suml // => i _.
    by rewrite rpredMn ?mem_genField ?mem_nth // size_map sz_ps.
  apply: (fmorph_inj QsC); rewrite z1C Dz rmorph_sum; apply: eq_bigr => i _.
  by rewrite rmorphMn {1}Ds !(nth_map 0) ?sz_ps //= inQsK.
have [r [Dr mon_r] dv_r] := minCpolyP z; have nz_r := monic_neq0 mon_r.
have rz0: root (pQtoC r) z by rewrite dv_r.
have [q qz0 nz_q | QsV] := Wrap (VectMixin (min_subfx_vectAxiom rz0 nz_r _)).
  by rewrite dvdp_leq // -dv_r.
pose Qs := [FalgType rat of _ for VectType rat _ QsV].
exists [fieldExtType rat of Qs], (subfx_inj_rmorphism QtoC_M z r).
exists (subfx_eval _ z r 'X) => [|x].
  by rewrite /= subfx_inj_eval ?map_polyX ?hornerX.
have{x} [p ->] := subfxE x; exists p.
apply: (@fmorph_inj _ _ (subfx_inj_rmorphism _ z r)).
rewrite -horner_map -map_poly_comp [rhs in _ = rhs]subfx_inj_eval //.
congr _.[_]; last by rewrite /= subfx_inj_eval // map_polyX hornerX.
apply: eq_map_poly; exact: subfx_inj_base.
Qed.

Definition in_Crat_span s x :=
  exists a : rat ^ size s, x = \sum_i QtoC (a i) * s`_i.

Fact Crat_span_subproof s x : decidable (in_Crat_span s x).
Proof.
have [Qxs [QxsC [[|x1 s1] // [<- <-] {x s} _]]] := num_field_exists (x :: s).
have QxsC_Z a z: QxsC (a *: z) = QtoC a * QxsC z.
  rewrite mulrAC; apply: (canRL (mulfK _)); first by rewrite intr_eq0 denq_eq0.
  by rewrite mulrzr mulrzl -!rmorphMz scalerMzl -mulrzr -numqE scaler_int.
apply: decP (x1 \in <<in_tuple s1>>%VS) _; rewrite /in_Crat_span size_map.
apply: (iffP idP) => [/coord_span-> | [a Dx]].
  move: (coord _) => a; exists [ffun i => a i x1]; rewrite rmorph_sum.
  by apply: eq_bigr => i _; rewrite ffunE (nth_map 0).
have{Dx} ->: x1 = \sum_i a i *: s1`_i.
  apply: (fmorph_inj QxsC); rewrite Dx rmorph_sum.
  by apply: eq_bigr => i _; rewrite QxsC_Z (nth_map 0).
by apply: memv_suml => i _; rewrite memvZ ?memv_span ?mem_nth.
Qed.

Definition Crat_span s : pred algC := Crat_span_subproof s.
Lemma Crat_spanP s x : reflect (in_Crat_span s x) (x \in Crat_span s).
Proof. exact: sumboolP. Qed.
Fact Crat_span_key s : pred_key (Crat_span s). Proof. by []. Qed.
Canonical Crat_span_keyed s := KeyedPred (Crat_span_key s).

Lemma mem_Crat_span s : {subset s <= Crat_span s}.
Proof.
move=> _ /(nthP 0)[ix ltxs <-]; pose i0 := Ordinal ltxs.
apply/Crat_spanP; exists [ffun i => (i == i0)%:R].
rewrite (bigD1 i0) //= ffunE eqxx // rmorph1 mul1r.
by rewrite big1 ?addr0 // => i; rewrite ffunE rmorph_nat mulr_natl => /negbTE->.
Qed.

Fact Crat_span_zmod_closed s : zmod_closed (Crat_span s).
Proof.
split=> [|_ _ /Crat_spanP[x ->] /Crat_spanP[y ->]].
  apply/Crat_spanP; exists 0.
  by apply/esym/big1=> i _; rewrite ffunE rmorph0 mul0r.
apply/Crat_spanP; exists (x - y); rewrite -sumrB; apply: eq_bigr => i _.
by rewrite -mulrBl -rmorphB !ffunE.
Qed.
Canonical Crat_span_opprPred s := OpprPred (Crat_span_zmod_closed s).
Canonical Crat_span_addrPred s := AddrPred (Crat_span_zmod_closed s).
Canonical Crat_span_zmodPred s := ZmodPred (Crat_span_zmod_closed s).

(* Automorphism extensions. *)
Lemma extend_algC_subfield_aut (Qs : fieldExtType rat)
  (QsC : {rmorphism Qs -> algC}) (phi : {rmorphism Qs -> Qs}) :
  {nu : {rmorphism algC -> algC} | {morph QsC : x / phi x >-> nu x}}.
Proof.
pose numF_inj (Qr : fieldExtType rat) := {rmorphism Qr -> algC}.
pose subAut := {Qr : _ & numF_inj Qr * {lrmorphism Qr -> Qr}}%type.
pose SubAut := existS _ _ (_, _) : subAut.
pose Sdom (mu : subAut) := projS1 mu.
pose Sinj (mu : subAut) : {rmorphism Sdom mu -> algC} := (projS2 mu).1.
pose Saut (mu : subAut) : {rmorphism Sdom mu -> Sdom mu} := (projS2 mu).2.
have SinjZ Qr (QrC : numF_inj Qr) a x: QrC (a *: x) = QtoC a * QrC x.
  rewrite mulrAC; apply: canRL (mulfK _) _.
    by rewrite intr_eq0 denq_neq0.
  by rewrite mulrzr mulrzl -!rmorphMz scalerMzl -scaler_int -mulrzr -numqE.
have Sinj_poly Qr (QrC : numF_inj Qr) p:
  map_poly QrC (map_poly (in_alg Qr) p) = pQtoC p.
- rewrite -map_poly_comp; apply: eq_map_poly => a.
  by rewrite /= SinjZ rmorph1 mulr1.
have ext1 mu0 x: {mu1 | exists y, x = Sinj mu1 y
  & exists2 in01 : {lrmorphism _}, Sinj mu0 =1 Sinj mu1 \o in01
  & {morph in01: y / Saut mu0 y >-> Saut mu1 y}}.
- pose b0 := vbasis {:Sdom mu0}.
  have [z _ /sig_eqW[[|px ps] // [Dx Ds]]] := algC_PET (x :: map (Sinj mu0) b0).
  have [p [_ mon_p] /(_ p) pz0] := minCpolyP z; rewrite dvdpp in pz0.
  have [r Dr] := closed_field_poly_normal (pQtoC p : {poly algC}).
  rewrite lead_coef_map {mon_p}(monicP mon_p) rmorph1 scale1r in Dr.
  have{pz0} rz: z \in r by rewrite -root_prod_XsubC -Dr.
  have [Qr [QrC [rr Drr genQr]]] := num_field_exists r.
  have{rz} [zz Dz]: {zz | QrC zz = z}.
    by move: rz; rewrite -Drr => /mapP/sig2_eqW[zz]; exists zz.
  have{ps Ds} [in01 Din01]: {in01 : {lrmorphism _} | Sinj mu0 =1 QrC \o in01}.
    have in01P y: {yy | Sinj mu0 y = QrC yy}.
      exists (\sum_i coord b0 i y *: (map_poly (in_alg Qr) ps`_i).[zz]).
      rewrite {1}(coord_vbasis (memvf y)) !rmorph_sum; apply: eq_bigr => i _.
      rewrite !SinjZ; congr (_ * _); rewrite -(nth_map _ 0) ?size_tuple // Ds.
      rewrite -horner_map Dz Sinj_poly (nth_map 0) //.
      by have:= congr1 size Ds; rewrite !size_map size_tuple => <-.
    pose in01 y := sval (in01P y).
    have Din01 y: Sinj mu0 y = QrC (in01 y) by rewrite /in01; case: (in01P y).
    suffices in01M: lrmorphism in01 by exists (LRMorphism in01M).
    pose rwM := (=^~ Din01, SinjZ, rmorph1, rmorphB, rmorphM).
    by do 3?split; try move=> ? ?; apply: (fmorph_inj QrC); rewrite !rwM.
  have {z zz Dz px Dx} Dx: exists xx, x = QrC xx.
    exists (map_poly (in_alg Qr) px).[zz].
    by rewrite -horner_map Dz Sinj_poly Dx.
  pose lin01 := linfun in01; pose K := (lin01 @: fullv)%VS.
  have memK y: reflect (exists yy, y = in01 yy) (y \in K).
    apply: (iffP memv_imgP) => [[yy _ ->] | [yy ->]];
      by exists yy; rewrite ?lfunE ?memvf.
  have algK: has_algid K && (K * K <= K)%VS.
    rewrite has_algid1; last by apply/memK; exists 1; rewrite rmorph1.
    apply/prodvP=> _ _ /memK[y1 ->] /memK[y2 ->].
    by apply/memK; exists (y1 * y2); rewrite rmorphM.
  have ker_in01: lker lin01 == 0%VS.
    by apply/lker0P=> y1 y2; rewrite !lfunE; apply: fmorph_inj.
  pose f := (lin01 \o linfun (Saut mu0) \o lin01^-1)%VF.
  have Df y: f (in01 y) = in01 (Saut mu0 y).
    transitivity (f (lin01 y)); first by rewrite !lfunE.
    by do 4!rewrite lfunE /=; rewrite lker0_lfunK.
  have hom_f: kHom 1 (ASpace algK) f.
    apply/kHomP; split=> [_ /vlineP[a ->] | _ _ /memK[y1 ->] /memK[y2 ->]].
      by rewrite -(rmorph1 in01) -linearZ /= Df {1}linearZ /= rmorph1.
    by rewrite -rmorphM !Df !rmorphM.
  pose pr := map_poly (in_alg Qr) p.
  have Qpr: pr \is a polyOver 1%VS.
    by apply/polyOverP=> i; rewrite coef_map memvZ ?memv_line.
  have splitQr: splittingFieldFor K pr fullv.
    apply: splittingFieldForS (sub1v (ASpace algK)) _; exists rr => //.
    congr (_ %= _): (eqpxx pr); apply: (@map_poly_inj _ _ QrC).
    rewrite Sinj_poly Dr -Drr big_map rmorph_prod; apply: eq_bigr => zz _.
    by rewrite rmorphB /= map_polyX map_polyC.
  have [f1 aut_f1 Df1]:= kHom_extends (sub1v (ASpace algK)) hom_f Qpr splitQr.
  pose nu := LRMorphism (LAut_lrmorph _ aut_f1).
  exists (SubAut Qr QrC nu) => //; exists in01 => //= y; rewrite -Df -Df1 //.
  by apply/memK; exists y.
have phiZ: scalable phi.
  move=> a y; do 2!rewrite -mulr_algl -in_algE.
  by rewrite -[a]divq_num_den !(fmorph_div, rmorphM, rmorph_int).
pose fix ext n :=
  if n is i.+1 then oapp (fun x => s2val (ext1 (ext i) x)) (ext i) (unpickle i)
  else SubAut Qs QsC (AddLRMorphism phiZ).
have mem_ext x n: (pickle x < n)%N -> {xx | Sinj (ext n) xx = x}.
  elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
  case: eqP => [<- _ | _ /IHn[xx <-]] {IHn}.
    apply: sig_eqW; rewrite pickleK /=; case: (ext1 _ x) => mu /= [xx ->] _.
    by exists xx.
  case: (unpickle n) => /= [y|]; last by exists xx.
  apply: sig_eqW; case: (ext1 _ y) => mu /= _ [in_mu inj_in_mu _].
  by exists (in_mu xx); rewrite inj_in_mu.
pose nu x := Sinj _ (Saut _ (sval (mem_ext x _ (ltnSn _)))).
have nu_inj n y: nu (Sinj (ext n) y) = Sinj (ext n) (Saut (ext n) y).
  rewrite /nu; case: (mem_ext _ _ _); move: _.+1 => n1 y1 Dy /=.
  without loss /subnK Dn1: n n1 y y1 Dy / (n <= n1)%N.
    by move=> IH; case/orP: (leq_total n n1) => /IH => [/(_ y) | /(_ y1)]->.
  elim: {n}(_ - n)%N {-1}n => [|k IHk] n in Dn1 y Dy *.
    by move: y1 Dy; rewrite -Dn1 => y1  /fmorph_inj ->.
  rewrite addSnnS in Dn1; move/IHk: Dn1 => /=.
  case: (unpickle _) => [z|] /=; last exact.
  case: (ext1 _ _) => mu /= _ [in_mu Dinj Daut].
  by rewrite Dy => /(_ _ (Dinj _))->; rewrite -Daut Dinj.
suffices nuM: rmorphism nu.
  by exists (RMorphism nuM) => x; rewrite /= (nu_inj 0%N).
pose le_nu (x : algC) n := (pickle x < n)%N.
have max3 x1 x2 x3: exists n, [/\ le_nu x1 n, le_nu x2 n & le_nu x3 n].
  exists (maxn (pickle x1) (maxn (pickle x2) (pickle x3))).+1.
  by apply/and3P; rewrite /le_nu !ltnS -!geq_max.
do 2?split; try move=> x1 x2.
- have [n] := max3 (x1 - x2) x1 x2.
  case=> /mem_ext[y Dx] /mem_ext[y1 Dx1] /mem_ext[y2 Dx2].
  rewrite -Dx nu_inj; rewrite -Dx1 -Dx2 -rmorphB in Dx.
  by rewrite (fmorph_inj _ Dx) !rmorphB -!nu_inj Dx1 Dx2.
- have [n] := max3 (x1 * x2) x1 x2.
  case=> /mem_ext[y Dx] /mem_ext[y1 Dx1] /mem_ext[y2 Dx2].
  rewrite -Dx nu_inj; rewrite -Dx1 -Dx2 -rmorphM in Dx.
  by rewrite (fmorph_inj _ Dx) !rmorphM -!nu_inj Dx1 Dx2.
by rewrite -(rmorph1 QsC) (nu_inj 0%N) !rmorph1.
Qed.

(* Should be in separable. *)
Lemma separable_Xn_sub_1 (R : idomainType) n :
  n%:R != 0 :> R -> @separablePolynomial R ('X^n - 1).
Proof.
case: n => [/eqP// | n nz_n]; rewrite /separablePolynomial linearB /=.
rewrite derivC subr0 derivXn -scaler_nat coprimep_scaler //= exprS -scaleN1r.
rewrite coprimep_sym coprimep_addl_mul coprimep_scaler ?coprimep1 //.
by rewrite (signr_eq0 _ 1).
Qed.

Lemma C_prim_root_exists n : (n > 0)%N -> {z : algC | n.-primitive_root z}.
Proof.
pose p : {poly algC} := 'X^n - 1; have [r Dp] := closed_field_poly_normal p.
move=> n_gt0; apply/sigW; rewrite (monicP _) ?monic_Xn_sub_1 // scale1r in Dp.
have rn1: all n.-unity_root r by apply/allP=> z; rewrite -root_prod_XsubC -Dp.
have sz_r: (n < (size r).+1)%N.
  by rewrite -(size_prod_XsubC r id) -Dp size_Xn_sub_1.
have [|z] := hasP (has_prim_root n_gt0 rn1 _ sz_r); last by exists z.
by rewrite -separable_prod_XsubC -Dp separable_Xn_sub_1 // -neq0N_neqC -lt0n.
Qed.

(* (Integral) Cyclotomic polynomials. *)

Definition Cyclotomic n : {poly int} :=
  let: exist z _ := C_prim_root_exists (ltn0Sn n.-1) in
  map_poly CtoZ (cyclotomic z n).

Notation "''Phi_' n" := (Cyclotomic n)
  (at level 8, n at level 2, format "''Phi_' n").

Lemma Cyclotomic_monic n : 'Phi_n \is monic.
Proof.
rewrite /'Phi_n; case: (C_prim_root_exists _) => z /= _.
rewrite monicE lead_coefE coef_map_id0 ?(int_algC_K 0) //.
by rewrite size_poly_eq -lead_coefE (monicP (cyclotomic_monic _ _)) (CintrK 1).
Qed.

Lemma Cintr_Cyclotomic n z :
  n.-primitive_root z -> pZtoC 'Phi_n = cyclotomic z n.
Proof.
elim: {n}_.+1 {-2}n z (ltnSn n) => // m IHm n z0 le_mn prim_z0.
rewrite /'Phi_n; case: (C_prim_root_exists _) => z /=.
have n_gt0 := prim_order_gt0 prim_z0; rewrite prednK // => prim_z.
have [uDn _ inDn] := divisors_correct n_gt0.
pose q := \prod_(d <- rem n (divisors n)) 'Phi_d.
have mon_q: q \is monic by apply: monic_prod => d _; exact: Cyclotomic_monic.
have defXn1: cyclotomic z n * pZtoC q = 'X^n - 1.
  rewrite (prod_cyclotomic prim_z) (big_rem n) ?inDn //=.
  rewrite divnn n_gt0 rmorph_prod /=; congr (_ * _).
  apply: eq_big_seq => d; rewrite mem_rem_uniq ?inE //= inDn => /andP[n'd ddvn].
  rewrite -IHm ?dvdn_prim_root // -ltnS (leq_ltn_trans _ le_mn) //.
  by rewrite ltn_neqAle n'd dvdn_leq.
have mapXn1 (R1 R2 : ringType) (f : {rmorphism R1 -> R2}):
  map_poly f ('X^n - 1) = 'X^n - 1.
- by rewrite rmorphB /= rmorph1 map_polyXn.
have nz_q: pZtoC q != 0.
  by rewrite -size_poly_eq0 size_map_inj_poly // size_poly_eq0 monic_neq0.
have [r def_zn]: exists r, cyclotomic z n = pZtoC r.
  have defZtoC: ZtoC =1 QtoC \o ZtoQ by move=> a; rewrite /= rmorph_int.
  have /dvdpP[r0 Dr0]: map_poly ZtoQ q %| 'X^n - 1.
    rewrite -(dvdp_map QtoC_M) mapXn1 -map_poly_comp.
    by rewrite -(eq_map_poly defZtoC) -defXn1 dvdp_mull.
  have [r [a nz_a Dr]] := rat_poly_scale r0.
  exists (unscale_int_poly r); apply: (mulIf nz_q); rewrite defXn1.
  rewrite -rmorphM -(unscale_int_monic mon_q) -unscale_int_polyM /=.
  have ->: r * q = a *: ('X^n - 1).
    apply: (map_inj_poly (intr_inj : injective ZtoQ)) => //.
    rewrite map_polyZ mapXn1 Dr0 Dr -scalerAl scalerKV ?intr_eq0 //.
    by rewrite rmorphM.
  by rewrite unscale_int_polyZ // unscale_int_monic ?monic_Xn_sub_1 ?mapXn1.
rewrite getCintpK; last first.
  by apply/(all_nthP 0)=> i _; rewrite def_zn coef_map isIntC_int.
pose f e (k : 'I_n) := Ordinal (ltn_pmod (k * e) n_gt0).
have [e Dz0] := prim_rootP prim_z (prim_expr_order prim_z0).
have co_e_n: coprime e n by rewrite -(prim_root_exp_coprime e prim_z) -Dz0.
have injf: injective (f e).
  apply: can_inj (f (egcdn e n).1) _ => k; apply: val_inj => /=.
  rewrite modnMml -mulnA -modnMmr -{1}(mul1n e).
  by rewrite (chinese_modr co_e_n 0) modnMmr muln1 modn_small.
rewrite [_ n](reindex_inj injf); apply: eq_big => k /=.
  by rewrite coprime_modl coprime_mull co_e_n andbT.
by rewrite prim_expr_mod // mulnC exprM -Dz0.
Qed.

Lemma prod_Cyclotomic n :
  (n > 0)%N -> \prod_(d <- divisors n) 'Phi_d = 'X^n - 1.
Proof.
move=> n_gt0; have [z prim_z] := C_prim_root_exists n_gt0.
apply: (map_inj_poly (intr_inj : injective ZtoC)) => //.
rewrite rmorphB rmorph1 rmorph_prod /= map_polyXn (prod_cyclotomic prim_z).
apply: eq_big_seq => d; rewrite -dvdn_divisors // => d_dv_n.
by rewrite -Cintr_Cyclotomic ?dvdn_prim_root.
Qed.

Lemma Cyclotomic0 : 'Phi_0 = 1.
Proof.
rewrite /'Phi_0; case: (C_prim_root_exists _) => z /= _.
by rewrite -[1]polyseqK /cyclotomic big_ord0 map_polyE !polyseq1 /= (CintrK 1).
Qed.

Lemma size_Cyclotomic n : size 'Phi_n = (totient n).+1.
Proof.
have [-> | n_gt0] := posnP n; first by rewrite Cyclotomic0 polyseq1.
have [z prim_z] := C_prim_root_exists n_gt0.
rewrite -(size_map_inj_poly (can_inj CintrK)) //.
rewrite (Cintr_Cyclotomic prim_z) -[_ n]big_filter filter_index_enum.
rewrite size_prod_XsubC -cardE totient_count_coprime big_mkord -sum1_card.
by congr _.+1; apply: eq_bigl => k; rewrite coprime_sym.
Qed.

Lemma minCpoly_cyclotomic n z :
  n.-primitive_root z -> minCpoly z = cyclotomic z n.
Proof.
move=> prim_z; have n_gt0 := prim_order_gt0 prim_z.
have Dpz := Cintr_Cyclotomic prim_z; set pz := cyclotomic z n in Dpz *.
have mon_pz: pz \is monic by exact: cyclotomic_monic.
have pz0: root pz z.
  have [|n_gt1|n1] := ltngtP n 1; first by rewrite ltnNge n_gt0.
    rewrite [pz](bigD1 (Ordinal n_gt1)) ?coprime1n //=.
    by rewrite rootM root_XsubC eqxx.
  rewrite /pz n1 [_ z _]big_ord1_cond root_XsubC expr0.
  by rewrite -(prim_expr_order prim_z) n1.
have [pf [Dpf mon_pf] dv_pf] := minCpolyP z.
have /dvdpP_rat_int[f [af nz_af Df] [g /esym Dfg]]: pf %| pZtoQ 'Phi_n.
  rewrite -dv_pf; congr (root _ z): pz0; rewrite -Dpz -map_poly_comp.
  by apply: eq_map_poly => b; rewrite /= rmorph_int.
without loss{nz_af} [mon_f mon_g]: af f g Df Dfg / f \is monic /\ g \is monic.
  move=> IH; pose cf := lead_coef f; pose cg := lead_coef g.
  have cfg1: cf * cg = 1.
    by rewrite -lead_coefM Dfg (monicP (Cyclotomic_monic n)).
  apply: (IH (af *~ cf) (f *~ cg) (g *~ cf)).
  - by rewrite rmorphMz -scalerMzr scalerMzl -mulrzA cfg1.
  - by rewrite mulrzAl mulrzAr -mulrzA cfg1.
  by rewrite !(intz, =^~ scaler_int) !monicE !lead_coefZ mulrC cfg1.
have{af Df} Df: pQtoC pf = pZtoC f.
  have:= congr1 lead_coef Df.
  rewrite lead_coefZ lead_coef_map_inj //; last exact: intr_inj.
  rewrite !(monicP _) // mulr1 Df => <-; rewrite scale1r -map_poly_comp.
  by apply: eq_map_poly => b; rewrite /= rmorph_int.
have [/size1_polyC Dg | g_gt1] := leqP (size g) 1.
  rewrite monicE Dg lead_coefC in mon_g.
  by rewrite -Dpz -Dfg Dg (eqP mon_g) mulr1 Dpf.
have [zk gzk0]: exists zk, root (pZtoC g) zk.
  have [rg] := closed_field_poly_normal (pZtoC g).
  rewrite lead_coef_map_inj // (monicP mon_g) scale1r => Dg.
  rewrite -(size_map_inj_poly (can_inj CintrK)) // Dg in g_gt1.
  rewrite size_prod_XsubC in g_gt1.
  by exists rg`_0; rewrite Dg root_prod_XsubC mem_nth.
have [k cokn Dzk]: exists2 k, coprime k n & zk = z ^+ k.
  have: root pz zk by rewrite -Dpz -Dfg rmorphM rootM gzk0 orbT.
  rewrite -[pz]big_filter -(big_map _ xpredT (fun a => _ - a%:P)).
  by rewrite root_prod_XsubC => /imageP[k]; exists k.
have co_fg (R : idomainType): n%:R != 0 :> R -> @coprimep R (intrp f) (intrp g).
  move=> nz_n; have: separablePolynomial (intrp ('X^n - 1) : {poly R}).
    by rewrite rmorphB rmorph1 /= map_polyXn separable_Xn_sub_1.
  rewrite -prod_Cyclotomic // (big_rem n) -?dvdn_divisors //= -Dfg.
  by rewrite !rmorphM /= !separable_mul => /and3P[] /and3P[].
suffices fzk0: root (pZtoC f) zk.
  have [] // := negP (coprimep_root (co_fg _ _) fzk0).
  by rewrite -neq0N_neqC -lt0n.
move: gzk0 cokn; rewrite {zk}Dzk; elim: {k}_.+1 {-2}k (ltnSn k) => // m IHm k.
rewrite ltnS => lekm gzk0 cokn.
have [|k_gt1] := leqP k 1; last have [p p_pr /dvdnP[k1 Dk]] := pdivP k_gt1.
  rewrite -[leq k 1](mem_iota 0 2) !inE => /pred2P[k0 | ->]; last first.
    by rewrite -Df dv_pf.
  have /eqP := size_Cyclotomic n; rewrite -Dfg size_Mmonic ?monic_neq0 //.
  rewrite k0 /coprime gcd0n in cokn; rewrite (eqP cokn).
  rewrite -(size_map_inj_poly (can_inj CintrK)) // -Df -Dpf.
  by rewrite -(subnKC g_gt1) -(subnKC (size_minCpoly z)) !addnS.
move: cokn; rewrite Dk coprime_mull => /andP[cok1n].
rewrite prime_coprime // (dvdn_charf (char_Fp p_pr)) => /co_fg {co_fg}.
have charFpX: p \in [char {poly 'F_p}].
  by rewrite (rmorph_char (polyC_rmorphism _)) ?char_Fp.
rewrite -(coprimep_pexpr _ _ (prime_gt0 p_pr)) -(Frobenius_autE charFpX).
rewrite -[g]comp_polyXr map_comp_poly -horner_map /= Frobenius_autE -rmorphX.
rewrite -!map_poly_comp (@eq_map_poly _ _ _ (polyC \o *~%R 1)); last first.
  by move=> a; rewrite /= !rmorph_int.
rewrite map_poly_comp -[_.[_]]map_comp_poly /= => co_fg.
suffices: coprimep (pZtoC f) (pZtoC (g \Po 'X^p)).
  move/coprimep_root=> /=/(_ (z ^+ k1))/implyP.
  rewrite map_comp_poly map_polyXn horner_comp hornerXn.
  rewrite -exprM -Dk [_ == 0]gzk0 implybF => /negP[].
  have: root pz (z ^+ k1).
    rewrite -[pz]big_filter -(big_map _ xpredT (fun a => _ - a%:P)).
    rewrite filter_index_enum root_prod_XsubC; apply/imageP.
    exists (Ordinal (ltn_pmod k1 n_gt0)); rewrite ?unfold_in ?coprime_modl //=.
    by rewrite prim_expr_mod.
  rewrite -Dpz -Dfg rmorphM rootM => /orP[] //= /IHm-> //.
  rewrite (leq_trans _ lekm) // -[k1]muln1 Dk ltn_pmul2l ?prime_gt1 //.
  by have:= ltnW k_gt1; rewrite Dk muln_gt0 => /andP[].
suffices: coprimep f (g \Po 'X^p).
  case/Bezout_coprimepP=> [[u v]]; rewrite -size_poly_eq1.
  rewrite -(size_map_inj_poly (can_inj CintrK)) // rmorphD !rmorphM /=.
  rewrite size_poly_eq1 => {co_fg}co_fg; apply/Bezout_coprimepP.
  by exists (pZtoC u, pZtoC v).
apply: contraLR co_fg => /coprimepPn[|d]; first exact: monic_neq0.
rewrite andbC -size_poly_eq1 dvdp_gcd => /and3P[sz_d].
pose d1 := unscale_int_poly d.
have d_dv_mon h: d %| h -> h \is monic -> exists h1, h = d1 * h1.
  case/ID.dvdpP=> [[c h1] /= nz_c Dh] mon_h; exists (unscale_int_poly h1).
  by rewrite -unscale_int_polyM mulrC -Dh unscale_int_polyZ ?unscale_int_monic.
case/d_dv_mon=> // f1 Df1 /d_dv_mon[|f2 ->].
  rewrite monicE lead_coefE size_comp_poly size_polyXn /=.
  rewrite comp_polyE coef_sum polySpred ?monic_neq0 //= mulnC.
  rewrite big_ord_recr /= -lead_coefE (monicP mon_g) scale1r.
  rewrite -exprM coefXn eqxx big1 ?add0r // => i _.
  rewrite coefZ -exprM coefXn eqn_pmul2l ?prime_gt0 //.
  by rewrite eqn_leq leqNgt ltn_ord mulr0.
have monFp h: h \is monic -> size (map_poly ( *~%R 1) h) = size h.
  by move=> mon_h; rewrite size_poly_eq // -lead_coefE (monicP mon_h) oner_eq0.
apply/coprimepPn; last exists (map_poly ( *~%R 1) d1).
  by rewrite -size_poly_eq0 monFp // size_poly_eq0 monic_neq0.
rewrite Df1 !rmorphM dvdp_gcd !dvdp_mulr //= -size_poly_eq1.
rewrite monFp ?size_unscale_int_poly //.
rewrite monicE [_ d1]intEsign (negPf (negz_lead_unscale_int_poly d)).
have/esym/eqP := congr1 (absz \o lead_coef) Df1.
by rewrite /= (monicP mon_f) lead_coefM abszM muln_eq1 => /andP[/eqP-> _].
Qed.

(* Extended automorphisms of Q_n. *)
Lemma Qn_Aut_exists k n :
    coprime k n ->
  {u : {rmorphism algC -> algC} | forall z, z ^+ n = 1 -> u z = z ^+ k}.
Proof.
have [-> /eqnP | n_gt0 co_k_n] := posnP n.
  by rewrite gcdn0 => ->; exists [rmorphism of idfun].
have [z prim_z] := C_prim_root_exists n_gt0.
have [Qn [QnC [[|zn []] // [Dz]]] genQn] := num_field_exists [:: z].
pose Q1 := aspace1 Qn; pose phi := kHomExtend Q1 \1%VF zn (zn ^+ k).
have homQn1: kHom Q1 Q1 \1%VF by rewrite kHom1.
have pzn_zk0: root (map_poly \1%VF (minPoly Q1 zn)) (zn ^+ k).
  rewrite -(fmorph_root QnC) rmorphX Dz -map_poly_comp.
  rewrite (@eq_map_poly _ _ _ QnC) => [|a]; last by rewrite /= id_lfunE.
  set p1 := map_poly _ _.
  have [q1 Dp1]: exists q1, p1 = pQtoC q1.
    have a_ i: (minPoly Q1 zn)`_i \in Q1.
      (* :BUG: v8.4 on the inferance of Q1 ... again *)
      by apply/(@polyOverP _ Q1); exact: minPolyOver.
    have{a_} a_ i := sig_eqW (vlineP _ _ (a_ i)).
    exists (\poly_(i < size (minPoly Q1 zn)) sval (a_ i)).
    apply/polyP=> i; rewrite coef_poly coef_map coef_poly /=.
    case: ifP => _; rewrite ?rmorph0 //; case: (a_ i) => a /= ->.
    apply: canRL (mulfK _) _; first by rewrite intr_eq0 denq_eq0.
    rewrite mulrzr -rmorphMz scalerMzl -mulrzr -numqE scaler_int.
    by rewrite rmorph_int.
  have: root p1 z by rewrite -Dz fmorph_root root_minPoly.
  rewrite Dp1; have [q2 [Dq2 _] ->] := minCpolyP z.
  case/dvdpP=> r1 ->; rewrite rmorphM rootM /= -Dq2; apply/orP; right.
  rewrite (minCpoly_cyclotomic prim_z) /cyclotomic.
  rewrite (bigD1 (Ordinal (ltn_pmod k n_gt0))) ?coprime_modl //=.
  by rewrite rootM root_XsubC prim_expr_mod ?eqxx.
have phiM: lrmorphism phi.
  by apply/LAut_lrmorph; rewrite -genQn /= kHomExtendkHom.
have [nu Dnu] := extend_algC_subfield_aut QnC (RMorphism phiM).
exists nu => _ /(prim_rootP prim_z)[i ->].
rewrite rmorphX exprAC -Dz -Dnu /= -{1}[zn]hornerX /phi.
rewrite (kHomExtend_poly homQn1) ?polyOverX //.
rewrite map_polyE map_id_in => [|?]; last by rewrite id_lfunE.
by rewrite polyseqK hornerX rmorphX.
Qed.

Lemma group_num_field_exists (gT : finGroupType) (G : {group gT}) :
  {Qn : fieldExtType rat & {QnC : {rmorphism Qn -> algC} &
    {nQn : isNormalFieldExt Qn & galois nQn 1 fullv
         & forall nuQn : argumentType (mem (Aut nQn fullv 1)),
              {nu : {rmorphism algC -> algC} |
                 {morph QnC: a / val (repr nuQn) a >-> nu a}}}
  & {w : Qn & #|G|.-primitive_root w /\ Fadjoin 1 w = fullv
       & forall (hT : finGroupType) (H : {group hT}) (phi : 'CF(H)),
         is_char phi -> forall x, (#[x] %| #|G|)%N -> {a | QnC a = phi x}}}}.
Proof.
have [z prim_z] := C_prim_root_exists (cardG_gt0 G); set n := #|G| in prim_z *.
have [Qn [QnC [[|w []] // [Dz] genQn]]] := num_field_exists [:: z].
have prim_w: n.-primitive_root w by rewrite -Dz fmorph_primitive_root in prim_z.
exists Qn, QnC; last first.
  exists w => // hT H phi Nphi x x_dv_n.
  apply: sig_eqW; have [rH ->] := is_charP Nphi.
  have [Hx | /cfun0->] := boolP (x \in H); last by exists 0; rewrite rmorph0.  
  have [e [_ [enx1 _] [-> _] _]] := repr_rsim_diag rH Hx.
  have /fin_all_exists[k Dk] i: exists k, e 0 i = z ^+ k.
    have [|k ->] := (prim_rootP prim_z) (e 0 i); last by exists k.
    by have /dvdnP[q ->] := x_dv_n; rewrite mulnC exprM enx1 expr1n.
  exists (\sum_i w ^+ k i); rewrite rmorph_sum; apply/eq_bigr => i _.
  by rewrite rmorphX Dz Dk.
have Q_Xn1: ('X^n - 1 : {poly Qn}) \is a polyOver 1%VS.
  by rewrite rpredB ?rpred1 ?rpredX //= polyOverX.
have splitXn1: splittingFieldFor 1 ('X^n - 1) {:Qn}.
  pose r := codom (fun i : 'I_n => w ^+ i).
  have Dr: 'X^n - 1 = \prod_(y <- r) ('X - y%:P).
    by rewrite -(factor_Xn_sub_1 prim_w) big_mkord big_map enumT.
  exists r; first by rewrite -Dr eqpxx.
  apply/eqP; rewrite eqEsubv subvf -genQn genFieldSr //; apply/allP=> /=.
  by rewrite andbT -root_prod_XsubC -Dr; apply/unity_rootP/prim_expr_order.
have [|nQn GalQn] := splitting_field_galois Q_Xn1 splitXn1.
  apply: separable_Xn_sub_1; rewrite -(fmorph_eq0 QnC) rmorph_nat.
  by rewrite -neq0N_neqC -lt0n cardG_gt0.
exists nQn => // nuQn; case: {nuQn}(repr _) => f /= /LAut_is_enum fM.
exact: (extend_algC_subfield_aut QnC (LRMorphism fM)).
Qed.

(* Integral spans. *)

Lemma int_Smith_normal_form m n (M : 'M[int]_(m, n)) :
  {L : 'M_m & {R : 'M[int]_n & {d : seq nat | sorted dvdn d &
     let D := \matrix_(i, j) ((nth 0%N d i)%:Z *+ (i == j :> nat))
       in M = L *m D *m R}
     & R \in unitmx} & L \in unitmx}.
Proof.
pose absM m1 n1 (A : 'M_(m1, n1)) ij := `|A ij.1 ij.2|%N.
pose maxM A := \max_ij absM _ _ A ij.
have maxM_max A ij: (absM _ _ A ij <= maxM _ _ A)%N by exact: leq_bigmax.
pose minM A :=
  let mA := maxM _ _ A in let aA := absM _ _  A in
  (mA - \max_(ij | aA ij != 0) (mA - aA ij))%N.
have divZ x y: (x %| `|y|)%N -> {u | y = u * x%:Z}.
  move=> x_dv_y; exists ((-1) ^+ negz y * Posz (`|y| %/ x)).
  by rewrite -mulrA -PoszM divnK -?intEsign.
have BezoutZ x y (d := gcdn `|x| `|y|):
  {u : int * int & {v | u.1 * v.1 + u.2 * v.2 = 1}
                   & u.1 * d = x /\ u.2 * d = y}.
- have [x0 | nz_x] := eqVneq x 0.
    do 2?exists (0, (-1) ^+ negz y); first by rewrite -signr_addb addbb.
    by rewrite /d x0 gcd0n -intEsign.
  have [[u1 Dx] [u2 Dy]]:= (divZ d x (dvdn_gcdl _ _), divZ d y (dvdn_gcdr _ _)).
  rewrite -absz_gt0 in nz_x; exists (u1, u2) => //.
  have [v2 _ /dvdnP/sig_eqW/=[v1 Dd]] := Bezoutl `|y| nz_x.
  exists ((-1) ^+ negz x * v1%:Z, - ((-1) ^+ negz y * v2%:Z)) => /=.
  apply: (@mulfI _ d%:Z); first by rewrite -lt0n gcdn_gt0 nz_x.
  rewrite mulrN mulr1 mulrBr mulrCA mulrA -Dx mulrCA {2}[x]intEsign -mulrA.
  rewrite signrMK mulrCA mulrA -Dy mulrCA {2}[y]intEsign -mulrA signrMK.
  by rewrite -!PoszM mulnC -Dd -/d mulnC PoszD addrK.
move: {2}_.+1 (ltnSn (m + n)) => mn.
elim: mn => // mn IHmn in m n M *; rewrite ltnS => le_mn.
move: {2}_.+1 (ltnSn (minM m n M)) => G.
elim: G => // G IHg in m n M le_mn *; move Dg: (minM m n M) => g gleG.
have [ij nz_ij | no_ij] := pickP (fun ij => absM _ _ M ij != 0%N); last first.
  do 2![exists 1%:M; try exact: unitmx1]; exists nil; rewrite //= mulmx1 mul1mx.
  apply/matrixP=> i j; apply/eqP; rewrite mxE nth_nil mul0rn -absz_eq0.
  exact: negbFE (no_ij (i, j)).
have{ij nz_ij Dg} [i [j nz_g Dg]]: {i : _ & {j | g != 0%N & `|M i j|%N = g}}.
  rewrite -Dg /minM (bigmax_eq_arg ij) ?subKn //.
  by case: arg_maxP => // [[i j]]; exists i, j. 
do [case: m i => [[]//|m] i; case: n j => [[]//|n] j] in M Dg le_mn *.
wlog [k gdv']: m n M i j Dg le_mn / {k | ~~ (g %| `|M i k|)}%N; last first.
  wlog Dj: j k M gdv' Dg / j = 0; last rewrite {j}Dj in Dg.
    case/(_ 0 (tperm j 0 k) (xcol j 0 M)); rewrite ?mxE ?tpermK ?tpermR //.
    move=> L [R [d dvD dM] uR] uL; exists L => //.
    exists (xcol j 0 R); last by rewrite xcolE unitmx_mul uR unitmx_perm.
    exists d; rewrite //= xcolE !mulmxA -dM xcolE -mulmxA -perm_mxM tperm2.
    by rewrite perm_mx1 mulmx1.
  have nz_k: k != 0 by apply: contraNneq gdv' => ->; rewrite Dg.
  case: n => [[[]//]|n] in k le_mn nz_k M gdv' Dg *.
  wlog{nz_k} Dk: k M gdv' Dg / k = 1; last rewrite {k}Dk in Dg gdv'.
    case/(_ 1 (xcol k 1 M)); rewrite ?mxE ?tpermR ?tpermD //.
    move=> L [R [d dvD dM] uR] uL; exists L => //.
    exists (xcol k 1 R); last by rewrite xcolE unitmx_mul uR unitmx_perm.
    exists d; rewrite //= xcolE !mulmxA -dM xcolE -mulmxA -perm_mxM tperm2.
    by rewrite perm_mx1 mulmx1.
  do [set x := M i 0; set y := M i 1] in gdv' Dg.
  have [[ux uy] [[vx vy] /= Euv][]] := BezoutZ x y; set g1 := gcdn _ _ => Dx Dy.
  have g1ltG: (g1 < G)%N.
    rewrite -ltnS (leq_trans _ gleG) // ltnS ltn_neqAle dvdn_leq ?lt0n //.
      by rewrite (contraNneq _ gdv') // => <-; exact: dvdn_gcdr.
    by rewrite -Dg dvdn_gcdl.
  pose t2 := [fun k => [tuple _; _]`_k : int].
  pose Uul := \matrix_(k, l < 2) t2 (t2 vx (- uy) l) (t2 vy ux l) k.
  pose U : 'M_(2 + n) := block_mx Uul 0 0 1%:M; pose M1 := M *m U.
  have uU: U \in unitmx.
    rewrite unitmxE det_ublock det1 (expand_det_col _ 0) big_ord_recl big_ord1.
    do 2!rewrite /cofactor [row' _ _]mx11_scalar !mxE det_scalar1 /=.
    by rewrite mulr1 mul1r mulN1r opprK mulrC (mulrC vy) Euv.
  have M1i0: absM _ _ M1 (i, 0) = g1.
    rewrite /M1 -(lshift0 n 1) [U]block_mxEh mul_mx_row /absM row_mxEl.
    rewrite -[M](@hsubmxK _ _ 2) (@mul_row_col _ _ 2) mulmx0 addr0 !mxE /=.
    rewrite big_ord_recl big_ord1 !mxE /= [lshift _ _]((_ =P 0) _) // -/x.
    rewrite [lshift _ _]((_ =P 1) _) // -/y -Dx -Dy !(mulrAC _ g1%:Z).
    by rewrite -mulrDl Euv mul1r.
  have [|L [R [dd dv_dd dM1] uR] uL] := IHg _ _ M1 le_mn.
    apply: leq_ltn_trans g1ltG; rewrite leq_subLR -(addnC g1) -leq_subLR.
    by rewrite (bigmax_sup (i, 0)) ?M1i0 // -lt0n gcdn_gt0 lt0n Dg nz_g.
  exists L => //.
  exists (R *m invmx U); last by rewrite unitmx_mul uR unitmx_inv.
  by exists dd => //; rewrite mulmxA -dM1 mulmxK.
move=> IHdvd.
wlog [Di Dj]: i j M Dg / i = 0 /\ j = 0; last rewrite {i}Di {j}Dj in Dg.
  case/(_ 0 0 (xrow i 0 (xcol j 0 M))); rewrite ?mxE ?tpermR //.
  move=> L [R [d dvD dM] uR] uL.
  exists (xrow i 0 L); last by rewrite xrowE unitmx_mul unitmx_perm.
  exists (xcol j 0 R); last by rewrite xcolE unitmx_mul uR unitmx_perm.
  exists d; rewrite //= xcolE xrowE -!mulmxA (mulmxA L) (mulmxA _ R) -dM xcolE.
  by rewrite xrowE !mulmxA -mulmxA -!perm_mxM !tperm2 !perm_mx1 mulmx1 mul1mx.
have [k gdv' | dvg0] := pickP (fun k => ~~ (g %| `|M 0%R k|)%N).
  by apply: IHdvd Dg le_mn _; exists k.
without loss{dvg0} eq00: M Dg / forall k, M 0 k = M 0 0.
  move=> IH0; have div0 := divZ _ _ (negbFE (dvg0 _)).
  pose Uur := col' 0 (\row_k (1 - (-1) ^+ negz (M 0 0) * sval (div0 k))).
  pose U : 'M_(1 + n) := block_mx 1 Uur 0 1%:M; pose M1 := M *m U.
  have uU: U \in unitmx by rewrite unitmxE det_ublock !det1 mulr1.
  have M10k k: M1 0 k = M 0 0.
    rewrite /M1 -{1}(lshift0 m 0) -{1}[M](@submxK _ 1 _ 1).
    rewrite (@mulmx_block _ 1 m 1) (@col_mxEu _ 1) !mulmx1 mulmx0 addr0.
    rewrite [ulsubmx _]mx11_scalar mul_scalar_mx !mxE !lshift0.
    case: splitP => [k0 _ | k1 Dk]; rewrite ?ord1 !mxE // lshift0 rshift1.
    rewrite mulrBr mulr1 mulrCA {3}[M 0 0]intEsign Dg -mulrA signrMK mulrC.
    by case: (div0 _) => _ <-; exact: subrK.
  have [|k|L [R [d dvD dM] uR] uL] := IH0 M1; rewrite ?M10k //.
  exists L => //; exists (R * U^-1); last by rewrite unitmx_mul uR unitmx_inv.
  by exists d; rewrite //= mulmxA -dM mulmxK.
have [[i j] gdv' | {eq00}dvgM] := pickP (fun ij => ~~ (g %| absM _ _ M ij)%N).
  have [] := IHdvd _ _ M^T j 0; rewrite ?mxE ?eq00 1?addnC //.
    by exists i; rewrite mxE.
  move=> L [R [d dvD dM] uR] uL.
  exists R^T; first exists L^T; rewrite ?unitmx_tr //; exists d => //.
  rewrite -[M]trmxK dM !trmx_mul mulmxA; congr (_ *m _ *m _).
  by apply/matrixP=> i1 j1; rewrite !mxE eq_sym; case: eqP => // ->.
have [|g_gt1|{dvgM}g1] := ltngtP g 1; first by rewrite ltnNge lt0n nz_g.
  have dv_g := divZ _ _ (negbFE (dvgM (_, _))); have g_gt0 := ltnW g_gt1.
  pose M1 := \matrix_(i, j) sval (dv_g i j).
  have dM: M = g%:Z *: M1.
    by apply/matrixP=> i j; rewrite !mxE mulrC; case: (dv_g _ _).
  have [|L [R [d dvD dM1] uR] uL] := IHg _ _ M1 le_mn.
    rewrite -ltnS (leq_trans _ gleG) // ltnS (leq_trans _ g_gt1) // ltnS.
    have M1_00: absM _ _ M1 (0, 0) = 1%N.
      by apply/eqP; rewrite -(eqn_pmul2l g_gt0) -(abszM g) muln1 -{2}Dg dM !mxE.
    by rewrite leq_subLR addnC -leq_subLR (bigmax_sup (0, 0)) ?M1_00.
  exists L => //; exists R => //; exists [seq g * a | a <- d]%N.
    case: d dvD {dM1} => //= a d; elim: d a => //= a1 d IHd a0 /andP[a01 /IHd].
    by rewrite dvdn_pmul2l ?a01.
  rewrite dM dM1 scalemxAl scalemxAr; congr (_ *m _ *m _).
  apply/matrixP=> i j; rewrite !mxE mulrnAr.
  have [lt_i_d | le_d_i] := ltnP i (size d); first by rewrite (nth_map 0%N).
  by rewrite !nth_default ?size_map ?mulr0.
rewrite {nz_g gleG G IHg IHdvd}g1 -[m.+1]/(1 + m)%N -[n.+1]/(1 + n)%N in M Dg *.
pose a := M 0 0; pose u := ursubmx M; pose v := dlsubmx M.
have{g Dg} a2: a * a = 1 by rewrite -expr2 [a]intEsign Dg mulr1 sqrr_sign.
have Da: ulsubmx M = a%:M by rewrite [_ M]mx11_scalar !mxE !lshift0.
pose M1 := - (v *m (a *: u)) + drsubmx M.
have [|L [R [d dvD dM1] uR uL]] := IHmn m n M1; first by rewrite -addnS ltnW.
exists (block_mx a%:M 0 v L); last first.
  rewrite unitmxE det_lblock unitrM det_scalar1 -(@unitrX_pos _ _ 2) //.
  by rewrite expr2 a2 unitr1.
exists (block_mx 1 (a *: u) 0 R); last first.
  by rewrite unitmxE det_ublock det_scalar1 mul1r.
exists (1%N :: d) => [|D]; set D1 := \matrix_(i, j) _ in dM1.
  by rewrite /= path_min_sorted // => g _; exact: dvd1n.
have ->: D = block_mx 1 0 0 D1.
  by apply/matrixP=> i j; do 3?[rewrite ?mxE ?ord1 //=; case: splitP=> ? ->].
rewrite !mulmx_block !(mul0mx, mulmx0, addr0) !mulmx1 add0r mul_scalar_mx.
by rewrite -Da scalerA a2 scale1r -dM1 addNKr submxK.
Qed.

Definition inIntSpan (V : zmodType) m (s : m.-tuple V) v :=
  exists a : int ^ m, v = \sum_(i < m) s`_i *~ a i.

Lemma dec_Qint_span (V : vectType rat) m (s : m.-tuple V) v :
  decidable (inIntSpan s v).
Proof.
have s_s (i : 'I_m): s`_i \in <<s>>%VS by rewrite memv_span ?memt_nth.
have s_Zs a: \sum_(i < m) s`_i *~ a i \in <<s>>%VS.
  by rewrite memv_suml // => i _; rewrite -scaler_int memvZ.
case s_v: (v \in <<s>>%VS); last by right=> [[a Dv]]; rewrite Dv s_Zs in s_v.
pose S := \matrix_(i < m, j < _) coord (vbasis <<s>>) j s`_i.
pose r := \rank S; pose k := (m - r)%N; pose Em := erefl m.
have Dm: (m = k + r)%N by rewrite subnK ?rank_leq_row.
have [K kerK]: {K : 'M_(k, m) | map_mx ZtoQ K == kermx S}%MS.
  pose B := row_base (kermx S); pose d := \prod_ij denq (B ij.1 ij.2).
  exists (castmx (mxrank_ker S, Em) (map_mx (fun x => numq x) (ZtoQ d *: B))).
  rewrite /k; case: _ / (mxrank_ker S); set B1 := map_mx _ _.
  have ->: B1 = (ZtoQ d *: B).
    apply/matrixP=> i j; rewrite 3!mxE mulrC [d](bigD1 (i, j)) // rmorphM mulrA.
    by rewrite -numqE -rmorphM numq_int.
  suffices nz_d: d%:Q != 0 by rewrite !eqmx_scale // !eq_row_base andbb.
  by rewrite intr_eq0; apply/prodf_neq0 => i _; exact: denq_neq0.
have [L [G [D _ defK] uG] _] := int_Smith_normal_form K.
pose Gud := castmx (Dm, Em) G; pose G'lr := castmx (Em, Dm) (invmx G).
have{K L D defK kerK} kerGu: map_mx ZtoQ (usubmx Gud) *m S = 0.
  pose Kl := map_mx ZtoQ (lsubmx (castmx (erefl k, Dm) (K *m invmx G))).
  have{defK} defK: map_mx ZtoQ K = row_mx Kl 0 *m map_mx ZtoQ Gud.
    rewrite -[K](mulmxKV uG) -{2}[G](castmxK Dm Em) -/Gud.
    rewrite -[K *m _](castmxK (erefl k) Dm) map_mxM map_castmx.
    rewrite -(hsubmxK (castmx _ _)) map_row_mx -/Kl map_castmx /Em.
    set Kr := map_mx _ _; case: _ / (esym Dm) (map_mx _ _) => /= GudQ.
    congr (row_mx _ _ *m _); apply/matrixP=> i j; rewrite !mxE defK mulmxK //=.
    rewrite castmxE mxE big1 //= => j1 _; rewrite mxE /= eqn_leq andbC.
    by rewrite leqNgt (leq_trans (valP j1)) ?mulr0 ?leq_addr.
  have /row_full_inj: row_full Kl; last apply.
    rewrite /row_full eqn_leq rank_leq_row /= -{1}[k](mxrank_ker S).
    rewrite -(eqmxP kerK) defK map_castmx mxrankMfree; last first.
      case: _ / (Dm); apply/row_freeP; exists (map_mx ZtoQ (invmx G)).
      by rewrite -map_mxM mulmxV ?map_mx1.
    by rewrite -mxrank_tr tr_row_mx trmx0 -addsmxE addsmx0 mxrank_tr.
  rewrite mulmx0 mulmxA (sub_kermxP _) // -(eqmxP kerK) defK.
  by rewrite -{2}[Gud]vsubmxK map_col_mx mul_row_col mul0mx addr0.
pose T := map_mx ZtoQ (dsubmx Gud) *m S.
have{kerGu} defS: map_mx ZtoQ (rsubmx G'lr) *m T = S.
  have: G'lr *m Gud = 1%:M by rewrite /G'lr /Gud; case: _ / (Dm); exact: mulVmx.
  rewrite -{1}[G'lr]hsubmxK -[Gud]vsubmxK mulmxA mul_row_col -map_mxM.
  move/(canRL (addKr _))->; rewrite -mulNmx raddfD /= map_mx1 map_mxM /=.
  by rewrite mulmxDl -mulmxA kerGu mulmx0 add0r mul1mx.
pose vv := \row_j coord (vbasis <<s>>) j v.
have uS: row_full S.
  apply/row_fullP; exists (\matrix_(i, j) coord s j (vbasis <<s>>)`_i).
  apply/matrixP=> j1 j2; rewrite !mxE.
  rewrite -(coord_free _ _ (basis_free (vbasisP _))).
  rewrite -!tnth_nth (coord_span (vbasis_mem (mem_tnth j1 _))) linear_sum.
  by apply: eq_bigr => i _; rewrite !mxE (tnth_nth 0) !linearZ.
have eqST: (S :=: T)%MS by apply/eqmxP; rewrite -{1}defS !submxMl.
case Zv: (map_mx (fun x => denq x) (vv *m pinvmx T) == const_mx 1).
  pose a := map_mx (fun x => numq x) (vv *m pinvmx T) *m dsubmx Gud.
  left; exists [ffun j => a 0 j].
  transitivity (\sum_j (map_mx ZtoQ a *m S) 0 j *: (vbasis <<s>>)`_j).
    rewrite {1}(coord_vbasis s_v); apply: eq_bigr => j _; congr (_ *: _).
    have ->: map_mx ZtoQ a = vv *m pinvmx T *m map_mx ZtoQ (dsubmx Gud).
      rewrite map_mxM /=; congr (_ *m _); apply/rowP=> i; rewrite 2!mxE numqE.
      by have /eqP/rowP/(_ i) := Zv; rewrite !mxE => ->; rewrite mulr1.
    by rewrite -(mulmxA _ _ S) mulmxKpV ?mxE // -eqST submx_full.
  rewrite (coord_vbasis (s_Zs _)); apply: eq_bigr => j _; congr (_ *: _).
  rewrite linear_sum mxE; apply: eq_bigr => i _.
  by rewrite -scaler_int linearZ [a]lock !mxE ffunE.
right=> [[a Dv]]; case/eqP: Zv; apply/rowP.
have ->: vv = map_mx ZtoQ (\row_i a i) *m S.
  apply/rowP=> j; rewrite !mxE Dv linear_sum.
  by apply: eq_bigr => i _; rewrite -scaler_int linearZ !mxE.
rewrite -defS -2!mulmxA; have ->: T *m pinvmx T = 1%:M.
  have uT: row_free T by rewrite /row_free -eqST.
  by apply: (row_free_inj uT); rewrite mul1mx mulmxKpV.
by move=> i; rewrite mulmx1 -map_mxM 2!mxE denq_int mxE.
Qed.

Lemma dec_Cint_span (V : vectType algC) m (s : m.-tuple V) v :
  decidable (inIntSpan s v).
Proof.
have s_s (i : 'I_m): s`_i \in <<s>>%VS by rewrite memv_span ?memt_nth.
have s_Zs a: \sum_(i < m) s`_i *~ a i \in <<s>>%VS.
  by rewrite memv_suml // => i _; rewrite -scaler_int memvZ.
case s_v: (v \in <<s>>%VS); last by right=> [[a Dv]]; rewrite Dv s_Zs in s_v.
pose IzT := {: 'I_m * 'I_(\dim <<s>>)}; pose Iz := 'I_#|IzT|.
pose b := vbasis <<s>>.
pose z_s := [image coord b ij.2 (tnth s ij.1) | ij <- IzT].
pose rank2 j i: Iz := enum_rank (i, j); pose val21 (p : Iz) := (enum_val p).1.
pose inQzs w := forallb j, Crat_span z_s (coord b j w).
have enum_pairK j: {in predT, cancel (rank2 j) val21}.
  by move=> i; rewrite /val21 enum_rankK. 
have Qz_Zs a: inQzs (\sum_(i < m) s`_i *~ a i).
  apply/forallP=> j; apply/Crat_spanP; rewrite /in_Crat_span size_map -cardE.
  exists [ffun ij => (a (val21 ij))%:Q *+ ((enum_val ij).2 == j)].
  rewrite linear_sum {1}(reindex_onto _ _ (enum_pairK j)).
  rewrite big_mkcond; apply: eq_bigr => ij _ /=; rewrite nth_image (tnth_nth 0).
  rewrite (can2_eq (@enum_rankK _) (@enum_valK _)) ffunE -scaler_int /val21.
  case Dij: (enum_val ij) => [i j1]; rewrite xpair_eqE eqxx /= eq_sym -mulrb.
  by rewrite linearZ rmorphMn rmorph_int mulrnAl; case: eqP => // ->.
case Qz_v: (inQzs v); last by right=> [[a Dv]]; rewrite Dv Qz_Zs in Qz_v.
have [Qz [QzC [z1s Dz_s _]]] := num_field_exists z_s.
have sz_z1s: size z1s = #|IzT| by rewrite -(size_map QzC) Dz_s size_map cardE.
have xv j: {x | coord b j v = QzC x}.
  apply: sig_eqW; have /Crat_spanP[x ->] := forallP Qz_v j.
  exists (\sum_ij x ij *: z1s`_ij); rewrite rmorph_sum.
  apply: eq_bigr => ij _; rewrite mulrAC.
  apply: canLR (mulfK _) _; first by rewrite intr_eq0 denq_neq0.
  rewrite mulrzr -rmorphMz scalerMzl -(mulrzr (x _)) -numqE scaler_int.
  by rewrite rmorphMz mulrzl -(nth_map _ 0) ?Dz_s // -(size_map QzC) Dz_s.
pose sz := [tuple [ffun j => z1s`_(rank2 j i)] | i < m].
have [Zsv | Zs'v] := dec_Qint_span sz [ffun j => sval (xv j)].
  left; have{Zsv} [a Dv] := Zsv; exists a.
  transitivity (\sum_j \sum_(i < m) QzC ((sz`_i *~ a i) j) *: b`_j).
    rewrite {1}(coord_vbasis s_v) -/b; apply: eq_bigr => j _.
    rewrite -scaler_suml; congr (_ *: _).
    have{Dv} /ffunP/(_ j) := Dv; rewrite sum_ffunE !ffunE -rmorph_sum => <-.
    by case: (xv j).
  rewrite exchange_big; apply: eq_bigr => i _.
  rewrite (coord_vbasis (s_s i)) -/b mulrz_suml; apply: eq_bigr => j _.
  rewrite scalerMzl ffunMzE rmorphMz; congr ((_ *~ _) *: _).
  rewrite nth_mktuple ffunE -(nth_map _ 0) ?sz_z1s // Dz_s.
  by rewrite nth_image enum_rankK /= (tnth_nth 0).
right=> [[a Dv]]; case: Zs'v; exists a.
apply/ffunP=> j; rewrite sum_ffunE !ffunE; apply: (fmorph_inj QzC).
case: (xv j) => /= _ <-; rewrite Dv linear_sum rmorph_sum.
apply: eq_bigr => i _; rewrite nth_mktuple raddfMz !ffunMzE rmorphMz ffunE.
by rewrite -(nth_map _ 0 QzC) ?sz_z1s // Dz_s nth_image enum_rankK -tnth_nth.
Qed.

Definition Cint_span (s : seq algC) : pred algC :=
  fun x => dec_Cint_span (in_tuple [seq \row_(i < 1) y | y <- s]) (\row_i x).
Fact Cint_span_key s : pred_key (Cint_span s). Proof. by []. Qed.
Canonical Cint_span_keyed s := KeyedPred (Cint_span_key s).

Lemma Cint_spanP n (s : n.-tuple algC) x :
  reflect (inIntSpan s x) (x \in Cint_span s).
Proof.
rewrite unfold_in /Cint_span; case: (dec_Cint_span _ _) => [Zs_x | Zs'x] /=.
  left; have{Zs_x} [] := Zs_x; rewrite /= size_map size_tuple => a /rowP/(_ 0).
  rewrite !mxE => ->; exists a; rewrite summxE; apply: eq_bigr => i _.
  by rewrite -scaler_int (nth_map 0) ?size_tuple // !mxE mulrzl.
right=> [[a Dx]]; have{Zs'x} [] := Zs'x.
rewrite /inIntSpan /= size_map size_tuple; exists a.
apply/rowP=> i0; rewrite !mxE summxE Dx; apply: eq_bigr => i _.
by rewrite -scaler_int mxE mulrzl (nth_map 0) ?size_tuple // !mxE.
Qed.

Lemma mem_Cint_span s : {subset s <= Cint_span s}.
Proof.
move=> _ /(nthP 0)[ix ltxs <-]; apply/(Cint_spanP (in_tuple s)).
exists [ffun i => i == Ordinal ltxs : int].
rewrite (bigD1 (Ordinal ltxs)) //= ffunE eqxx.
by rewrite big1 ?addr0 // => i; rewrite ffunE => /negbTE->.
Qed.

Lemma Cint_span_zmod_closed s : zmod_closed (Cint_span s).
Proof.
have sP := Cint_spanP (in_tuple s); split=> [|_ _ /sP[x ->] /sP[y ->]].
  by apply/sP; exists 0; rewrite big1 // => i; rewrite ffunE.
apply/sP; exists (x - y); rewrite -sumrB; apply: eq_bigr => i _.
by rewrite !ffunE raddfB.
Qed.
Canonical Cint_span_opprPred s := OpprPred (Cint_span_zmod_closed s).
Canonical Cint_span_addrPred s := AddrPred (Cint_span_zmod_closed s).
Canonical Cint_span_zmodPred s := ZmodPred (Cint_span_zmod_closed s).

(* Algebraic integers. *)

Definition algInt : pred algC := fun x => all isIntC (minCpoly x).
Fact algInt_key : pred_key algInt. Proof. by []. Qed.
Canonical algInt_keyed := KeyedPred algInt_key.

Lemma root_monic_algInt p x :
  root p x -> p \is monic -> all isIntC p -> x \in algInt.
Proof.
have pZtoQtoC pz: pQtoC (pZtoQ pz) = pZtoC pz.
  by rewrite -map_poly_comp; apply: eq_map_poly => b; rewrite /= rmorph_int.
move=> px0 mon_p /getCintpP[pz Dp]; rewrite unfold_in.
move: px0; rewrite Dp -pZtoQtoC /algInt; have [q [-> mon_q] ->] := minCpolyP x.
case/dvdpP_rat_int=> qz [a nz_a Dq] [r].
move/(congr1 (fun q1 => lead_coef (a *: pZtoQ q1))).
rewrite rmorphM scalerAl -Dq lead_coefZ lead_coefM /=.
have /monicP->: pZtoQ pz \is monic by rewrite -(map_monic QtoC_M) pZtoQtoC -Dp.
rewrite (monicP mon_q) mul1r mulr1 lead_coef_map_inj //; last exact: intr_inj.
rewrite Dq => ->; apply/(all_nthP 0)=> i _; rewrite !(coefZ, coef_map).
by rewrite -rmorphM /= rmorph_int isIntC_int.
Qed.

Lemma Cint_rat_algInt z : z \in Crat -> z \in algInt -> isIntC z.
Proof.
case/CratP=> a ->{z} /(all_nthP 0)/(_ 0%N)/implyP.
have [p [Dp mon_p] dv_p] := minCpolyP (ratr a).
rewrite ltnW ?size_minCpoly // Dp coef_map.
suffices ->: p = ('X - a%:P) by rewrite polyseqXsubC /= rmorphN isIntC_opp.
have /irredp_XsubC: p %| 'X - a%:P by rewrite -dv_p fmorph_root root_XsubC.
rewrite -size_poly_eq1 -(size_map_poly QtoC_M) -Dp.
by rewrite eqn_leq leqNgt size_minCpoly eqpMP ?monicXsubC //= => /eqP.
Qed.

Lemma algInt_Cint x : isIntC x -> x \in algInt.
Proof.
move=> Zx; apply: root_monic_algInt (monicXsubC x) _.
  by rewrite root_XsubC eqxx.
by rewrite polyseqXsubC /= isIntC_opp Zx isIntC_1.
Qed.

Lemma algInt_int x : x%:~R \in algInt.
Proof. by rewrite algInt_Cint ?isIntC_int. Qed.

Lemma algInt0 : 0 \in algInt. Proof. exact: (algInt_int 0). Qed.
Lemma algInt1 : 1 \in algInt. Proof. exact: (algInt_int 1). Qed.
Hint Resolve algInt0 algInt1.

Lemma algInt_unity_root n x : (n > 0)%N -> n.-unity_root x -> x \in algInt.
Proof.
move=> n_gt0 xn1; apply: root_monic_algInt xn1 (monic_Xn_sub_1 _ n_gt0) _.
apply/(all_nthP 0)=> i _; rewrite coefB coefC -mulrb coefXn.
by rewrite isIntC_sub ?isIntC_nat.
Qed.

Lemma algInt_prim_root n z : n.-primitive_root z -> z \in algInt.
Proof.
move=> pr_z; apply/(algInt_unity_root (prim_order_gt0 pr_z))/unity_rootP.
exact: prim_expr_order.
Qed.

Lemma algInt_Cnat n : isNatC n -> n \in algInt.
Proof. by move/isIntC_Nat/algInt_Cint. Qed.

(* This is Isaacs, Lemma (3.3) *)
Lemma algInt_subring_exists (X : seq algC) :
    {subset X <= algInt} ->
  {S : pred algC &
     (*a*) subring_closed S
  /\ (*b*) {subset X <= S}
   & (*c*) {Y : {n : nat & n.-tuple algC} &
                {subset tagged Y <= S}
              & forall x, reflect (inIntSpan (tagged Y) x) (x \in S)}}.
Proof.
move=> AZ_X; pose m := (size X).+1.
pose n (i : 'I_m) := (size (minCpoly X`_i)).-2; pose N := (\max_i n i).+1.
pose IY := family (fun i => [pred e : 'I_N | e <= n i]%N).
have IY_0: 0 \in IY by apply/familyP=> // i; rewrite ffunE.
pose inIY := enum_rank_in IY_0.
pose Y := [image \prod_(i < m) X`_i ^+ (f : 'I_N ^ m) i | f <- IY].
have S_P := Cint_spanP [tuple of Y]; set S := Cint_span _ in S_P.
have sYS: {subset Y <= S} by exact: mem_Cint_span.
have S_1: 1 \in S.
  by apply/sYS/imageP; exists 0 => //; rewrite big1 // => i; rewrite ffunE.
have SmulX (i : 'I_m): {in S, forall x, x * X`_i \in S}.
  move=> _ /S_P[x ->]; rewrite mulr_suml rpred_sum // => j _.
  rewrite mulrzAl rpredMz {x}// nth_image mulrC (bigD1 i) //= mulrA -exprS.
  move: {j}(enum_val j) (familyP (enum_valP j)) => f fP.
  have:= fP i; rewrite inE /= leq_eqVlt => /predU1P[-> | fi_ltn]; last first.
    apply/sYS/imageP; have fiK: (inord (f i).+1 : 'I_N) = (f i).+1 :> nat.
      by rewrite inordK // ltnS (bigmax_sup i).
    exists (finfun [eta f with i |-> inord (f i).+1]).
      apply/familyP=> i1; rewrite inE ffunE /= fun_if fiK.
      by case: eqP => [-> // | _]; exact: fP.
    rewrite (bigD1 i isT) ffunE /= eqxx fiK; congr (_ * _).
    by apply: eq_bigr => i1; rewrite ffunE /= => /negPf->.
  have [/monicP ] := (minCpoly_monic X`_i, root_minCpoly X`_i).
  rewrite /root horner_coef lead_coefE -(subnKC (size_minCpoly _)) subn2.
  rewrite big_ord_recr /= addrC addr_eq0 => ->; rewrite mul1r => /eqP->.
  have /getCintpP[p Dp]: X`_i \in algInt.
    by have [/(nth_default 0)-> | /(mem_nth 0)/AZ_X] := leqP (size X) i.
  rewrite -/(n i) Dp mulNr rpredN // mulr_suml rpred_sum // => [[e le_e]] /= _.
  rewrite coef_map -mulrA mulrzl rpredMz ?sYS //; apply/imageP.
  have eK: (inord e : 'I_N) = e :> nat by rewrite inordK // ltnS (bigmax_sup i).
  exists (finfun [eta f with i |-> inord e]).
    apply/familyP=> i1; rewrite inE ffunE /= fun_if eK.
    by case: eqP => [-> // | _]; exact: fP.
  rewrite (bigD1 i isT) ffunE /= eqxx eK; congr (_ * _).
  by apply: eq_bigr => i1; rewrite ffunE /= => /negPf->.
exists S; last by exists (Tagged (fun n => n.-tuple _) [tuple of Y]).
split=> [|x Xx]; last first.
  by rewrite -[x]mul1r -(nth_index 0 Xx) (SmulX (Ordinal _)) // ltnS index_size.
split=> // x y Sx Sy; first by rewrite rpredB.
case/S_P: Sy => {y}[y ->]; rewrite mulr_sumr rpred_sum //= => j.
rewrite mulrzAr rpredMz {y}// nth_image; move: {j}(enum_val j) => f.
elim/big_rec: _ => [|i y _ IHy] in x Sx *; first by rewrite mulr1.
rewrite mulrA {y}IHy //.
elim: {f}(f i : nat) => [|e IHe] in x Sx *; first by rewrite mulr1.
by rewrite exprS mulrA IHe // SmulX.
Qed.

Section AlgIntSubring.

Import DefaultKeying GRing.DefaultPred.

(* This is Isaacs, Theorem (3.4). *)
Theorem fin_Csubring_algInt S n (Y : n.-tuple algC) :
     mulr_closed S -> (forall x, reflect (inIntSpan Y x) (x \in S)) ->
  {subset S <= algInt}.
Proof.
pose ZP : pred {poly algC} := fun p => all isIntC p.
have allcP (p : {poly algC}): reflect (forall i, isIntC p`_i) (p \in ZP).
  apply: (iffP (all_nthP 0)) => // IH i; have [/IH//|p_le_n] := ltnP i (size p).
  by rewrite nth_default ?isIntC_0.
have ZP_1: 1 \in ZP by rewrite unfold_in /ZP polyseq1 /= isIntC_1.
have ZP_X: 'X \in ZP by rewrite unfold_in /ZP polyseqX /= isIntC_1 isIntC_0.
have ringZP: subring_closed ZP.
  split=> // p q /allcP Zp /allcP Zq; apply/allcP=> i.
    by rewrite coefB isIntC_sub ?Zp ?Zq.
  by rewrite coefM isIntC_sum // => j _; rewrite isIntC_mul ?Zp ?Zq.
have [oppZP addZP] := (ringZP : oppr_closed ZP, ringZP : addr_closed ZP).
have mulZP : mulr_closed ZP := ringZP.
have ZP_C c: (ZtoC c)%:P \in ZP by rewrite raddfMz rpred_int.
move=> mulS S_P x Sx; pose v := \row_(i < n) Y`_i.
have [v0 | nz_v] := eqVneq v 0.
  case/S_P: Sx => {x}x ->; rewrite big1 ?isAlgInt0 // => i _.
  by have /rowP/(_ i) := v0; rewrite !mxE => ->; rewrite mul0rz.
have sYS (i : 'I_n): x * Y`_i \in S.
  by rewrite rpredM //; apply/S_P/Cint_spanP/mem_Cint_span/memt_nth.
pose A := \matrix_(i, j < n) sval (sig_eqW (S_P _ (sYS j))) i.
pose p := char_poly (map_mx ZtoC A).
have: p \in ZP.
  rewrite rpred_sum // => s _; rewrite rpredMsign rpred_prod // => j _.
  by rewrite !mxE /= rpredB ?rpredMn.
apply: root_monic_algInt (char_poly_monic _).
rewrite -eigenvalue_root_char; apply/eigenvalueP; exists v => //.
apply/rowP=> j; case dAj: (sig_eqW (S_P _ (sYS j))) => [a DxY].
by rewrite !mxE DxY; apply: eq_bigr => i _; rewrite !mxE dAj /= mulrzr.
Qed.

(* This is Isaacs, Corollary (3.5). *)
Corollary algInt_subring : subring_closed algInt.
Proof.
suff rAZ: {in algInt &, forall x y, (x - y \in algInt) * (x * y \in algInt)}.
  by split=> // x y AZx AZy; rewrite rAZ.
move=> x y AZx AZy.
have [|S [ringS] ] := @algInt_subring_exists [:: x; y]; first exact/allP/and3P.
move=> /allP/and3P[Sx Sy _] [Y _ genYS].
have AZ_S := fin_Csubring_algInt ringS genYS.
by have [_ S_B S_M] := ringS; rewrite !AZ_S ?S_B ?S_M.
Qed.
Canonical algInt_opprPred := OpprPred algInt_subring.
Canonical algInt_addrPred := AddrPred algInt_subring.
Canonical algInt_mulrPred := MulrPred algInt_subring.
Canonical algInt_zmodPred := ZmodPred algInt_subring.
Canonical algInt_semiringPred := SemiringPred algInt_subring.
Canonical algInt_smulrPred := SmulrPred algInt_subring.
Canonical algInt_subringPred := SubringPred algInt_subring.

End AlgIntSubring.

(* At last, some character theory. *)

Section IntegralChar.

Variables (gT : finGroupType) (G : {group gT}).

(* This is Isaacs, Corollary (3.6). *)
Lemma algInt_char (chi : 'CF(G)) x : is_char chi -> chi x \in algInt.
Proof.
have [Gx | /cfun0->//] := boolP (x \in G).
case/is_charP=> rG ->; have [e [_ [unit_e _] [-> _] _]] := repr_rsim_diag rG Gx.
rewrite rpred_sum // => i _; apply: (@algInt_unity_root #[x]) => //.
exact/unity_rootP.
Qed.

Lemma algInt_irr i x : 'chi[G]_i x \in algInt.
Proof. by apply: algInt_char; exact: irr_char. Qed.

Require Import vcharacter.

Lemma algInt_vchar phi x : phi \in 'Z[irr G] -> phi x \in algInt.
Proof.
case/vcharP=> [chi1 Nchi1 [chi2 Nchi2 ->]].
by rewrite !cfunE rpredB ?algInt_char.
Qed.

Section GenericClassSums.

(* This is Isaacs, Theorem (2.4), generalized to an arbitrary ring, and with  *)
(* the combinatorial definition of the coeficients exposed.                   *)
(* This part could move to mxrepresentation.*)

Variable F : fieldType.

Definition gring_classM_coef_set (Ki Kj : {set gT}) g :=
  [set xy \in [predX Ki & Kj] | let: (x, y) := xy in x * y == g]%g.

Definition gring_classM_coef (i j k : 'I_#|classes G|) :=
  #|gring_classM_coef_set (enum_val i) (enum_val j) (repr (enum_val k))|.

Definition gring_class_sum (i : 'I_#|classes G|) := gset_mx F G (enum_val i).

Local Notation "''K_' i" := (gring_class_sum i)
  (at level 8, i at level 2, format "''K_' i") : ring_scope.
Local Notation a := gring_classM_coef.

Lemma gring_class_sum_central i : ('K_i \in 'Z(group_ring F G))%MS.
Proof. by rewrite -classg_base_center (eq_row_sub i) // rowK. Qed.

Lemma set_gring_classM_coef (i j k : 'I_#|classes G|) g :
    g \in enum_val k ->
  a i j k = #|gring_classM_coef_set (enum_val i) (enum_val j) g|.
Proof.
rewrite /a; have /repr_classesP[] := enum_valP k; move: (repr _) => g1 Gg1 ->.
have [/imsetP[zi Gzi ->] /imsetP[zj Gzj ->]] := (enum_valP i, enum_valP j).
move=> g1Gg; have Gg := subsetP (class_subG Gg1 (subxx _)) _ g1Gg.
set Aij := gring_classM_coef_set _ _.
without loss suffices IH: g g1 Gg Gg1 g1Gg / (#|Aij g1| <= #|Aij g|)%N.
  by apply/eqP; rewrite eqn_leq !IH // class_sym.
have [w Gw Dg] := imsetP g1Gg; pose J2 (v : gT) xy := (xy.1 ^ v, xy.2 ^ v)%g.
have J2inj: injective (J2 w).
  by apply: can_inj (J2 w^-1)%g _ => [[x y]]; rewrite /J2 /= !conjgK.
rewrite -(card_imset _ J2inj) subset_leq_card //; apply/subsetP.
move=> _ /imsetP[[x y] /setIdP[/andP[/= x1Gx y1Gy] Dxy1] ->]; rewrite !inE /=.
rewrite !(class_sym _ (_ ^ _)) !classGidl // class_sym x1Gx class_sym y1Gy.
by rewrite -conjMg (eqP Dxy1) /= -Dg.
Qed.

Theorem gring_classM_expansion i j : 'K_i *m 'K_j = \sum_k (a i j k)%:R *: 'K_k.
Proof.
have [/imsetP[zi Gzi dKi] /imsetP[zj Gzj dKj]] := (enum_valP i, enum_valP j).
pose aG := regular_repr F G; have sKG := subsetP (class_subG _ (subxx G)).
transitivity (\sum_(x \in zi ^: G) \sum_(y \in zj ^: G) aG (x * y)%g).
  rewrite mulmx_suml -/aG dKi; apply: eq_bigr => x /sKG Gx.
  rewrite mulmx_sumr -/aG dKj; apply: eq_bigr => y /sKG Gy.
  by rewrite repr_mxM ?Gx ?Gy.
pose h2 xy : gT := (xy.1 * xy.2)%g.
pose h1 xy := enum_rank_in (classes1 G) (h2 xy ^: G).
rewrite pair_big (partition_big h1 xpredT) //=; apply: eq_bigr => k _.
rewrite (partition_big h2 (mem (enum_val k))) /= => [|[x y]]; last first.
  case/andP=> /andP[/= /sKG Gx /sKG Gy] /eqP <-.
  by rewrite enum_rankK_in ?class_refl ?mem_classes ?groupM ?Gx ?Gy.
rewrite scaler_sumr; apply: eq_bigr => g Kk_g; rewrite scaler_nat.
rewrite (set_gring_classM_coef _ _ Kk_g) -sumr_const; apply: eq_big => [] [x y].
  rewrite !inE /= dKi dKj /h1 /h2 /=; apply: andb_id2r => /eqP ->.
  have /imsetP[zk Gzk dKk] := enum_valP k; rewrite dKk in Kk_g.
  by rewrite (class_transr Kk_g) -dKk enum_valK_in eqxx andbT.
by rewrite /h2 /= => /andP[_ /eqP->].
Qed.

End GenericClassSums.

Definition gring_irr_mode (i : Iirr G) := locked (('chi_i 1%g)^-1 *: 'chi_i).

Arguments Scope gring_irr_mode [ring_scope group_scope].

Notation "''omega_' i [ A ]" := (xcfun (gring_irr_mode i) A)
   (at level 8, i at level 2, format "''omega_' i [ A ]") : ring_scope.

Notation "''K_' i" := (gring_class_sum _ i)
  (at level 8, i at level 2, format "''K_' i") : ring_scope.

Local Notation R_G := (group_ring algC G).
Local Notation a := gring_classM_coef.

(* This is Isaacs (2.25). *)
Lemma mx_irr_gring_op_center_scalar n (rG : mx_representation algC G n) A :
  mx_irreducible rG -> (A \in 'Z(R_G))%MS -> is_scalar_mx (gring_op rG A).
Proof.
move/groupC=> irrG /center_mxP[R_A cGA].
apply: mx_abs_irr_cent_scalar irrG _ _; apply/centgmxP => x Gx.
by rewrite -(gring_opG rG Gx) -!gring_opM ?cGA // envelop_mx_id.
Qed.

Section GringIrrMode.

Variable (i : Iirr G).
Let n := irr_degree (socle_of_Iirr i).
Let mxZn_inj: injective (@scalar_mx algC n).
Proof. by rewrite -[n]prednK ?irr_degree_gt0 //; exact: fmorph_inj. Qed.

Lemma cfRepr_gring_center n1 (rG : mx_representation algC G n1) A :
  cfRepr rG = 'chi_i -> (A \in 'Z(R_G))%MS -> gring_op rG A = 'omega_i[A]%:M.
Proof.
unlock gring_irr_mode => def_rG Z_A; rewrite xcfunZl -{2}def_rG xcfun_Repr.
have irr_rG: mx_irreducible rG.
  have sim_rG: mx_rsim 'Chi_i rG by apply: cfRepr_inj; rewrite cfun_Chi.
  exact: mx_rsim_irr sim_rG (socle_irr _).
have /is_scalar_mxP[e ->] := mx_irr_gring_op_center_scalar irr_rG Z_A.
congr _%:M; apply: (canRL (mulKf (irr1_neq0 i))).
by rewrite mulrC -def_rG cfunE repr_mx1 group1 -mxtraceZ scalemx1.
Qed.

Lemma irr_gring_center A :
  (A \in 'Z(R_G))%MS -> gring_op 'Chi_i A = 'omega_i[A]%:M.
Proof. exact: cfRepr_gring_center (cfun_Chi i). Qed.

Lemma gring_irr_modeM A B :
    (A \in 'Z(R_G))%MS -> (B \in 'Z(R_G))%MS ->
  'omega_i[A *m B] = 'omega_i[A] * 'omega_i[B].
Proof.
move=> Z_A Z_B; have [[R_A cRA] [R_B cRB]] := (center_mxP Z_A, center_mxP Z_B).
apply: mxZn_inj; rewrite scalar_mxM -!irr_gring_center ?gring_opM //.
apply/center_mxP; split=> [|C R_C]; first exact: envelop_mxM.
by rewrite mulmxA cRA // -!mulmxA cRB.
Qed.

Lemma gring_mode_class_sum_eq (k : 'I_#|classes G|) g :
  g \in enum_val k -> 'omega_i['K_k] = #|g ^: G|%:R * 'chi_i g / 'chi_i 1%g.
Proof.
have /imsetP[x Gx DxG] := enum_valP k; rewrite DxG => /imsetP[u Gu ->{g}].
unlock gring_irr_mode; rewrite classGidl ?cfunJ {u Gu}// mulrC mulr_natl.
rewrite xcfunZl raddf_sum DxG -sumr_const /=; congr (_ * _).
by apply: eq_bigr => _ /imsetP[u Gu ->]; rewrite xcfunG ?groupJ ?cfunJ.
Qed.

(* This is Isaacs, Theorem (3.7). *)
Lemma gring_mode_class_sum_algInt k : 'omega_i['K_k] \in algInt.
Proof.
move: k; pose X := [tuple 'omega_i['K_k] | k < #|classes G| ].
have memX k: 'omega_i['K_k] \in X by apply: map_f; exact: mem_enum.
have S_P := Cint_spanP X; set S := Cint_span X in S_P.
have S_X: {subset X <= S} by exact: mem_Cint_span.
have S_1: 1 \in S.
  apply: S_X; apply/imageP; exists (enum_rank_in (classes1 G) 1%g) => //.
  rewrite (@gring_mode_class_sum_eq _ 1%g) ?enum_rankK_in ?classes1 //.
  by rewrite mulfK ?irr1_neq0 // class1G cards1.
suffices Smul: mulr_closed S.
  by move=> k; apply: fin_Csubring_algInt S_P _ _; rewrite ?S_X.
split=> // _ _ /S_P[x ->] /S_P[y ->].
rewrite mulr_sumr rpred_sum // => j _.
rewrite mulrzAr mulr_suml rpredMz ?rpred_sum // => k _.
rewrite mulrzAl rpredMz {x y}// !nth_mktuple.
rewrite -gring_irr_modeM ?gring_class_sum_central //.
rewrite gring_classM_expansion raddf_sum rpred_sum // => jk _.
by rewrite scaler_nat raddfMn rpredMn ?S_X ?memX.
Qed.

(* A more useful form that does not involve the class sums. *)
Corollary class_div_irr1_algInt x :
  x \in G -> #|x ^: G|%:R * 'chi_i x / 'chi_i 1%g \in algInt.
Proof.
move=> Gx; have clGxG := mem_classes Gx; pose k := enum_rank_in clGxG (x ^: G).
have k_x: x \in enum_val k by rewrite enum_rankK_in // class_refl.
by rewrite -(gring_mode_class_sum_eq k_x) gring_mode_class_sum_algInt.
Qed.

Section MoreAlgCaut.

Implicit Type rR : unitRingType.

Lemma alg_num_field (Qz : fieldExtType rat) a : a%:A = ratr a :> Qz.
Proof. by rewrite -in_algE fmorph_eq_rat. Qed.

Lemma rmorphZ_num (Qz : fieldExtType rat) rR (f : {rmorphism Qz -> rR}) a x :
  f (a *: x) = ratr a * f x.
Proof. by rewrite -mulr_algl rmorphM alg_num_field fmorph_rat. Qed.

Lemma fmorph_numZ (Qz1 Qz2 : fieldExtType rat) (f : {rmorphism Qz1 -> Qz2}) :
  scalable f.
Proof. by move=> a x; rewrite rmorphZ_num -alg_num_field mulr_algl. Qed.
Definition NumLRmorphism Qz1 Qz2 f := AddLRMorphism (@fmorph_numZ Qz1 Qz2 f).

Implicit Type nu : {rmorphism algC -> algC}.

Lemma Crat_aut nu x : (nu x \in Crat) = (x \in Crat).
Proof.
apply/idP/idP=> /CratP[a] => [|->]; last by rewrite fmorph_rat ratr_Crat.
by rewrite -(fmorph_rat nu) => /fmorph_inj->; apply: ratr_Crat.
Qed.

Lemma aut_Crat nu : {in Crat, nu =1 id}.
Proof. by move=> _ /CratP[a ->]; apply: fmorph_rat. Qed.

Lemma algC_invaut_subproof nu x : {y | nu y = x}.
Proof.
have [r Dp] := closed_field_poly_normal (minCpoly x).
suffices /mapP/sig2_eqW[y _ ->]: x \in map nu r by exists y.
rewrite -root_prod_XsubC; congr (root _ x): (root_minCpoly x).
have [q [Dq _] _] := minCpolyP x; rewrite Dq -(eq_map_poly (fmorph_rat nu)).
rewrite (map_poly_comp nu) -{q}Dq Dp (monicP (minCpoly_monic x)) scale1r.
rewrite rmorph_prod big_map; apply: eq_bigr => z _.
by rewrite rmorphB /= map_polyX map_polyC.
Qed.
Definition algC_invaut nu x := sval (algC_invaut_subproof nu x).

Lemma algC_invautK nu : cancel (algC_invaut nu) nu.
Proof. by move=> x; rewrite /algC_invaut; case: algC_invaut_subproof. Qed.

Lemma algC_autK nu : cancel nu (algC_invaut nu).
Proof. exact: inj_can_sym (algC_invautK nu) (fmorph_inj nu). Qed.

Fact algC_invaut_is_rmorphism nu : rmorphism (algC_invaut nu).
Proof. exact: can2_rmorphism (algC_autK nu) (algC_invautK nu). Qed.
Canonical algC_invaut_additive nu := Additive (algC_invaut_is_rmorphism nu).
Canonical algC_invaut_rmorphism nu := RMorphism (algC_invaut_is_rmorphism nu).

Lemma minCpoly_aut (nu : {rmorphism algC -> algC}) x :
  minCpoly (nu x) = minCpoly x.
Proof.
wlog suffices dvd_nu: nu x / minCpoly x %| minCpoly (nu x).
  apply/eqP; rewrite -eqpMP ?minCpoly_monic //; apply/andP; split=> //.
  by rewrite -{2}(algC_autK nu x) dvd_nu.
have [[q [Dq _] min_q] [q1 [Dq1 _] _]] := (minCpolyP x, minCpolyP (nu x)).
rewrite Dq Dq1 dvdp_map -min_q -(fmorph_root nu) -map_poly_comp.
by rewrite (eq_map_poly (fmorph_rat nu)) -Dq1 root_minCpoly.
Qed.

Lemma algInt_aut nu x : (nu x \in algInt) = (x \in algInt).
Proof. by rewrite !unfold_in /algInt minCpoly_aut. Qed.

End MoreAlgCaut.

(* This is Isaacs, Theorem (3.8). *)
Theorem coprime_degree_support_cfcenter g :
    coprime (getNatC ('chi_i 1%g)) #|g ^: G| -> g \notin ('Z('chi_i))%CF ->
  'chi_i g = 0.
Proof.
set m := getNatC _ => co_m_gG notZg.
have [Gg | /cfun0-> //] := boolP (g \in G).
have Dm: 'chi_i 1%g = m%:R by apply/eqP/isNatC_irr1.
have m_gt0: (0 < m)%N by rewrite ltn_ltC -Dm ltC_irr1.
have nz_m: m%:R != 0 :> algC by rewrite -neq0N_neqC -lt0n.
pose alpha := 'chi_i g / m%:R.
have a_lt1: `|alpha| < 1.
  rewrite normC_mul normC_inv normC_nat -{2}(divff nz_m).
  rewrite ltCE (can_eq (mulfVK nz_m)) eq_sym -{1}Dm -irr_cfcenterE // notZg.
  by rewrite leC_pmul2r ?sposC_inv -?(ltn_ltC 0) // -Dm char1_ge_norm ?irr_char.
have Za: alpha \in algInt.
  have [u _ /dvdnP[v eq_uv]] := Bezoutl #|g ^: G| m_gt0.
  suffices ->: alpha = v%:R * 'chi_i g - u%:R * (alpha * #|g ^: G|%:R).
    rewrite rpredB // rpredM ?rpred_nat ?algInt_irr //.
    by rewrite mulrC mulrA -Dm class_div_irr1_algInt.
  rewrite -mulrCA -[v%:R](mulfK nz_m) -!natrM -eq_uv (eqnP co_m_gG).
  by rewrite mulrAC -mulrA -/alpha mulr_natl mulr_natr mulrS addrK.
have [Qn [QnC [nQn galQn gQnC] [_ _ Qn_g]]] := group_num_field_exists <[g]>.
have{Qn_g} [a Da]: exists a, QnC a = alpha.
  rewrite /alpha; have [a <-] := Qn_g _ G _ (irr_char i) g (dvdnn _).
  by exists (a / m%:R); rewrite fmorph_div rmorph_nat.
have Za_nu nu: sval (gQnC nu) alpha \in algInt by rewrite algInt_aut.
have norm_a_nu nu: `|sval (gQnC nu) alpha| <= 1.
  move: {nu}(sval _) => nu; rewrite fmorph_div rmorph_nat normC_mul normC_inv.
  rewrite normC_nat -Dm -(leC_pmul2r _ _ (ltC_irr1 (aut_Iirr nu i))) mul1r.
  congr (_ <= _): (char1_ge_norm g (irr_char (aut_Iirr nu i))).
  by rewrite !aut_IirrE !cfunE Dm rmorph_nat divfK.
pose beta := QnC (galoisNorm nQn 1 fullv a).
have Dbeta: beta = \prod_(nu \in Aut nQn fullv 1) sval (gQnC nu) alpha.
  rewrite /beta rmorph_prod; apply: eq_bigr => nu _.
  by case: (gQnC nu) => f /= ->; rewrite Da.
have Zbeta: isIntC beta.
  apply: Cint_rat_algInt; last by rewrite Dbeta rpred_prod.
  rewrite /beta; have /vlineP[/= c ->] := mem_galoisNorm galQn (memvf a).
  by rewrite alg_num_field fmorph_rat ratr_Crat.
have [|nz_a] := boolP (alpha == 0).
  by rewrite (can2_eq (divfK _) (mulfK _)) // mul0r => /eqP.
have: beta != 0 by rewrite Dbeta; apply/prodf_neq0 => nu _; rewrite fmorph_eq0.
move/(isIntC_normC_ge1 Zbeta); rewrite ltC_geF //; apply: leC_ltC_trans a_lt1.
rewrite -[`|alpha|]mulr1 Dbeta (bigD1 1%g) ?group1 //= -Da.
case: (gQnC _) => /= _ <-; rewrite repr_coset1 id_lfunE normC_mul.
rewrite -leC_sub -mulrBr posC_mul ?posC_norm // Da leC_sub.
elim/big_rec: _ => [|nu c _]; first by rewrite normC1 leC_refl.
apply: leC_trans; rewrite -leC_sub -{1}[`|c|]mul1r normC_mul -mulrBl.
by rewrite posC_mul ?posC_norm // leC_sub norm_a_nu.
Qed.

End GringIrrMode.

(* This is Isaacs, Theorem (3.9). *)
Import gseries.
Theorem primes_class_simple_gt1 C :
  simple G -> ~~ abelian G -> C \in (classes G)^# -> (size (primes #|C|) > 1)%N.
Proof.
move=> simpleG not_cGG /setD1P[ntC /imsetP[g Gg defC]].
have{ntC} nt_g: g != 1%g by rewrite defC classG_eq1 in ntC.
rewrite ltnNge {C}defC; set m := #|_|; apply/negP=> p_natC.
have{p_natC} [p p_pr [a Dm]]: {p : nat & prime p & {a | m = p ^ a}%N}.
  have /prod_prime_decomp->: (0 < m)%N by rewrite /m -index_cent1.
  rewrite prime_decompE; case Dpr: (primes _) p_natC => [|p []] // _.
    by exists 2 => //; rewrite big_nil; exists 0%N.
  rewrite big_seq1; exists p; last by exists (logn p m).
  by have:= mem_primes p m; rewrite Dpr mem_head => /esym/and3P[].
have{simpleG} [ntG minG] := simpleP _ simpleG.
pose p_dv1 i := dvdNC p ('chi[G]_i 1%g).
have p_dvd_supp_g i: ~~ p_dv1 i && (i != 0) -> 'chi_i g = 0.
  rewrite /p_dv1 irr1_degree dvdC_nat -prime_coprime // => /andP[co_p_i1 nz_i].
  have fful_i: cfker 'chi_i = [1].
    have /minG[//|/eqP] := cfker_normal 'chi_i.
    by rewrite eqEsubset subGcfker (negPf nz_i) andbF.
  have trivZ: 'Z(G) = [1] by have /minG[|/center_idP/idPn] := center_normal G.
  have trivZi: ('Z('chi_i))%CF = [1].
    apply/trivgP; rewrite -quotient_sub1 ?norms1 //= -fful_i cfcenter_eq_center.
    rewrite fful_i subG1 -(isog_eq1 (isog_center (quotient1_isog G))) /=.
    by rewrite trivZ.
  rewrite coprime_degree_support_cfcenter ?trivZi ?inE //.
  by rewrite -/m Dm irr1_degree getNatC_nat coprime_sym coprime_expl.
pose alpha := \sum_(i | p_dv1 i && (i != 0)) 'chi_i 1%g / p%:R * 'chi_i g.
have nz_p: p%:R != 0 :> algC by rewrite -neq0N_neqC -lt0n prime_gt0.
have Dalpha: alpha = - 1 / p%:R.
  apply/(canRL (mulfK nz_p))/eqP; rewrite -addr_eq0 addrC; apply/eqP/esym.
  transitivity (cfReg G g); first by rewrite cfRegE (negPf nt_g).
  rewrite cfReg_sum sum_cfunE (bigD1 0) //= chi0_1 !cfunE !cfun1E group1 Gg.
  rewrite mulr1; congr (1 + _); rewrite (bigID p_dv1) /= addrC big_andbC.
  rewrite big1 => [|i /p_dvd_supp_g chig0]; last by rewrite cfunE chig0 mulr0.
  rewrite add0r big_andbC mulr_suml; apply: eq_bigr => i _.
  by rewrite mulrAC divfK // cfunE.
suffices: dvdNC p 1 by rewrite (dvdC_nat p 1) dvdn1 -(subnKC (prime_gt1 p_pr)).
rewrite /dvdC (negPf nz_p) Cint_rat_algInt ?Crat_div ?rpred1 ?rpred_nat //.
rewrite -rpredN // -mulNr -Dalpha rpred_sum // => i /andP[/dvdCP[c Zc ->] _].
by rewrite mulfK // rpredM ?algInt_irr ?algInt_Cint.
Qed.

End IntegralChar.

Section MoreClassfun.

Lemma cfker_Morph_pre (gT rT : finGroupType) (A D : {group gT}) 
     (f : {morphism D >-> rT}) (phi : 'CF(f @* A)) :
   A \subset D -> cfker (cfMorph phi) = A :&: f @*^-1 (cfker phi).
Proof.
move=> sAD; apply/setP=> x; rewrite !inE; apply: andb_id2l => Ax.
have Dx := subsetP sAD x Ax; rewrite Dx mem_morphim //=.
apply/forallP/forallP=> Kx y.
  have [{y} /morphimP[y Dy Ay ->] | fA'y] := boolP (y \in f @* A).
    by rewrite -morphM // -!(cfMorphE phi) ?groupM.
  by rewrite !cfun0 ?groupMl // mem_morphim.
have [Ay | A'y] := boolP (y \in A); last by rewrite !cfun0 ?groupMl.
by rewrite !cfMorphE ?groupM ?morphM // (subsetP sAD).
Qed.

Lemma cfker_Mod_pre (gT : finGroupType) (G H : {group gT}) (phi : 'CF(G / H)) :
   G \subset 'N(H) -> cfker (phi %% H) = G :&: coset H @*^-1 (cfker phi).
Proof. exact: cfker_Morph_pre. Qed.

Lemma cfker_Quo (gT : finGroupType) (G H : {group gT}) (phi : 'CF(G)) :
  H <| G -> H \subset cfker (phi) -> cfker (phi / H) = (cfker phi / H)%g.
Proof.
move=> nsHG /cfQuoK {2}<- //; have [sHG nHG] := andP nsHG.
by rewrite cfker_Mod_pre 1?quotientGI // cosetpreK (setIidPr _) ?cfker_sub.
Qed.

Lemma cfaithful_Quo (gT : finGroupType) (G : {group gT}) (phi : 'CF(G)) :
  cfaithful (phi / cfker phi).
Proof. by rewrite cfaithfulE cfker_Quo ?cfker_normal ?trivg_quotient. Qed.

Lemma cfcenter_fful_irr (gT : finGroupType) (G : {group gT}) i :
  cfaithful 'chi[G]_i -> 'Z('chi_i)%CF = 'Z(G).
Proof.
move/trivgP=> Ki1; have:= cfcenter_eq_center i; rewrite {}Ki1.
have inj1: 'injm (@coset gT 1%g) by rewrite ker_coset.
by rewrite -injm_center; first apply: injm_morphim_inj; rewrite ?norms1.
Qed.

End MoreClassfun.

Section MoreIntegralChar.

Implicit Type gT : finGroupType.

Import gseries nilpotent abelian.

(* This is Burnside's famous p^a.q^b theorem (Isaacs, Theorem (3.10)). *)
Theorem Burnside_p_a_q_b gT (G : {group gT}) :
  (size (primes #|G|) <= 2)%N -> solvable G.
Proof.
move: {2}_.+1 (ltnSn #|G|) => n; elim: n => // n IHn in gT G *.
rewrite ltnS => leGn piGle2; have [simpleG | ] := boolP (simple G); last first.
  rewrite negb_forall_in => /exists_inP[N sNG]; rewrite eq_sym.
  have [-> | ] := altP (N =P G).
    rewrite groupP /= genGid normG andbT eqb_id negbK => /eqP->.
    exact: solvable1.
  rewrite [N == G]eqEproper sNG eqbF_neg !negbK => ltNG /and3P[grN].
  case/isgroupP: grN => {N}N -> in sNG ltNG *; rewrite /= genGid => ntN nNG.
  have nsNG: N <| G by exact/andP.
  have dv_le_pi m: (m %| #|G| -> size (primes m) <= 2)%N.
    move=> m_dv_G; apply: leq_trans piGle2.
    by rewrite uniq_leq_size ?primes_uniq //; apply: pi_of_dvd.
  rewrite (series_sol nsNG) !IHn ?dv_le_pi ?cardSg ?dvdn_quotient //.
    by apply: leq_trans leGn; apply: ltn_quotient.
  by apply: leq_trans leGn; apply: proper_card.
have [->|[p p_pr p_dv_G]] := trivgVpdiv G; first exact: solvable1.
have piGp: p \in \pi(G) by rewrite mem_primes p_pr cardG_gt0.
have [P sylP] := Sylow_exists p G; have [sPG pP p'GP] := and3P sylP.
have ntP: P :!=: 1%g by rewrite -rank_gt0 (rank_Sylow sylP) p_rank_gt0.
have /trivgPn[g /setIP[Pg cPg] nt_g]: 'Z(P) != 1%g.
  by rewrite center_nil_eq1 // (pgroup_nil pP).
apply: abelian_sol; have: (size (primes #|g ^: G|) <= 1)%N.
  rewrite -ltnS -[_.+1]/(size (p :: _)) (leq_trans _ piGle2) //.
  rewrite -index_cent1 uniq_leq_size // => [/= | q].
    rewrite primes_uniq -p'natEpi ?(pnat_dvd _ p'GP) ?indexgS //.
    by rewrite subsetI sPG sub_cent1.
  by rewrite inE => /predU1P[-> // |]; apply: pi_of_dvd; rewrite ?dvdn_indexg.
rewrite leqNgt; apply: contraR => /primes_class_simple_gt1-> //.
by rewrite !inE classG_eq1 nt_g mem_classes // (subsetP sPG).
Qed.

(* This is Isaacs, Theorem (3.11). *)
Theorem dvd_irr1_cardG gT (G : {group gT}) i : dvdC ('chi[G]_i 1%g) #|G|%:R.
Proof.
rewrite /dvdC -if_neg irr1_neq0 Cint_rat_algInt //=.
  by rewrite Crat_div ?rpred_nat // rpred_Cnat ?isNatC_irr1.
rewrite -(muln1 _ : #|G| * true = _)%N -(eqxx i) natrM.
rewrite -first_orthogonality_relation mulVKf ?neq0GC //.
rewrite sum_by_classes => [|x y Gx Gy]; rewrite -?conjVg ?cfunJ //.
rewrite mulr_suml rpred_sum // => K /repr_classesP[Gx {1}->].
by rewrite !mulrA mulrAC rpredM ?algInt_irr ?class_div_irr1_algInt.
Qed.

(* This is Isaacs, Theorem (3.12). *)
Theorem dvd_irr1_index_center gT (G : {group gT}) i :
  dvdC ('chi[G]_i 1%g) #|G : 'Z('chi_i)%CF|%:R.
Proof.
without loss fful: gT G i / cfaithful 'chi_i.
  rewrite -{1}[i](quo_IirrK _ (subxx _)) ?mod_IirrE ?cfModE ?cfker_normal //.
  rewrite morph1; set i1 := quo_Iirr _ i => /(_ _ _ i1) IH.
  have fful_i1: cfaithful 'chi_i1.
    by rewrite quo_IirrE ?cfker_normal ?cfaithful_Quo.
  have:= IH fful_i1; rewrite cfcenter_fful_irr // -cfcenter_eq_center.
  rewrite index_quotient_eq ?cfcenter_sub ?cfker_norm //.
  by rewrite setIC subIset // normal_sub ?cfker_center_normal.
have [lambda lin_lambda Dlambda] := cfcenter_Res 'chi_i.
have DchiZ: {in G & 'Z(G), forall x y, 'chi_i (x * y)%g = 'chi_i x * lambda y}.
  rewrite -(cfcenter_fful_irr fful) => x y Gx Zy.
  apply: (mulfI (irr1_neq0 i)); rewrite mulrCA.
  transitivity ('chi_i x * ('chi_i 1%g *: lambda) y); last by rewrite !cfunE.
  rewrite -Dlambda cfResE ?cfcenter_sub //.
  rewrite -cfun_Chi cfcenter_Repr !cfunE in Zy *.
  case/setIdP: Zy => Gy /is_scalar_mxP[e De].
  rewrite repr_mx1 group1 (groupM Gx Gy) (repr_mxM _ Gx Gy) Gx Gy De.
  by rewrite mul_mx_scalar mxtraceZ mulrCA mulrA mulrC -mxtraceZ scalemx1.
have inj_lambda: {in 'Z(G) &, injective lambda}.
  rewrite -(cfcenter_fful_irr fful) => x y Zx Zy eq_xy.
  apply/eqP; rewrite eq_mulVg1 -in_set1 (subsetP fful) // cfker_irrE inE.
  apply/eqP; transitivity ('Res['Z('chi_i)%CF] 'chi_i (x^-1 * y)%g).
    by rewrite cfResE ?cfcenter_sub // groupM ?groupV.
  rewrite Dlambda !cfunE lin_charM ?groupV // -eq_xy -lin_charM ?groupV //.
  by rewrite mulrC mulVg lin_char1 ?mul1r.
rewrite /dvdC -if_neg irr1_neq0 Cint_rat_algInt //.
  by rewrite Crat_div ?rpred_nat // rpred_Cnat ?isNatC_irr1.
rewrite (cfcenter_fful_irr fful) divgS_C ?center_sub //=.
have ->: #|G|%:R = \sum_(x \in G) 'chi_i x * 'chi_i (x^-1)%g.
  rewrite -[_%:R]mulr1; apply: canLR (mulVKf (neq0GC G)) _.
  by rewrite first_orthogonality_relation eqxx.
rewrite (big_setID [set x | 'chi_i x == 0]) /= -setIdE.
rewrite big1 ?add0r => [| x /setIdP[_ /eqP->]]; last by rewrite mul0r.
pose h x := (x ^: G * 'Z(G))%g; rewrite (partition_big_imset h).
rewrite !mulr_suml rpred_sum //= => _ /imsetP[x /setDP[Gx nz_chi_x] ->].
have: #|x ^: G|%:R * ('chi_i x * 'chi_i x^-1%g) / 'chi_i 1%g \in algInt.
  by rewrite !mulrA mulrAC rpredM ?algInt_irr ?class_div_irr1_algInt.
set X1 := (X in X / _ \in _); set X2 := (_ / _ as X in X / _ \in algInt).
congr (_ / _ \in algInt); apply: canRL (mulfK (neq0GC _)) _.
rewrite inE in nz_chi_x; rewrite {}/X1 {}/X2.
transitivity ('chi_i x * 'chi_i (x^-1)%g *+ #|h x|); last first.
  rewrite -sumr_const.
  apply: eq_big => [y | _ /mulsgP[_ z /imsetP[u Gu ->] Zz] ->].
    rewrite !inE -andbA; apply/idP/and3P=> [|[_ _ /eqP <-]]; last first.
      by rewrite -{1}[y]mulg1 mem_mulg ?class_refl.
    case/mulsgP=> _ z /imsetP[u Gu ->] Zz ->; have /centerP[Gz cGz] := Zz.
    rewrite groupM 1?DchiZ ?groupJ ?cfunJ //; split=> //.
      by rewrite mulf_neq0 // lin_char_neq0 /= ?cfcenter_fful_irr.
    rewrite -[z](mulKg u) -cGz // -conjMg /h classGidl {u Gu}//.
    apply/eqP/setP=> w; apply/mulsgP/mulsgP=> [][_ z1 /imsetP[v Gv ->] Zz1 ->].
      exists (x ^ v)%g (z * z1)%g; rewrite ?mem_imset ?groupM //.
      by rewrite conjMg -mulgA /(z ^ v)%g cGz // mulKg.
    exists ((x * z) ^ v)%g (z^-1 * z1)%g; rewrite ?mem_imset ?groupM ?groupV //.
    by rewrite conjMg -mulgA /(z ^ v)%g cGz // mulKg mulKVg.
  rewrite !irr_inv DchiZ ?groupJ ?cfunJ // rmorphM mulrAC !mulrA mulrAC -!mulrA.
  rewrite -!normCK normCK cfnorm_lin_char /= ?cfcenter_fful_irr // expr1n.
  by rewrite mulr1.
rewrite mulrAC -natrM mulr_natl; congr (_ *+ _).
symmetry; rewrite /h /mulg /= /set_mulg [in _ @2: (_, _)]unlock cardsE.
rewrite -cardX card_in_image // => [] [y1 z1] [y2 z2] /=.
move=> /andP[/=/imsetP[u1 Gu1 ->] Zz1] /andP[/=/imsetP[u2 Gu2 ->] Zz2] {y1 y2}.
move=> eq12; have /eqP := congr1 'chi_i eq12.
rewrite !(cfunJ, DchiZ) ?groupJ // (can_eq (mulKf nz_chi_x)).
rewrite (inj_in_eq inj_lambda) // => /eqP eq_z12; rewrite eq_z12 in eq12 *.
by rewrite (mulIg _ _ _ eq12).
Qed.

Lemma card_Iirr_abelian gT (G : {group gT}) : abelian G -> #|Iirr G| = #|G|.
Proof. by rewrite card_ord NirrE card_classes_abelian => /eqP. Qed.

(* This is Isaacs, exercise (2.16). *)
Lemma index_support_dvd_degree gT (G H : {group gT}) chi :
    H \subset G -> is_char chi -> chi \in 'CF(G, H) ->
    (H :==: 1%g) || abelian G ->
  dvdNC #|G : H| (chi 1%g).
Proof.
move=> sHG Nchi Hchi ZHG.
suffices: dvdNC #|G : H| ('Res[H] chi 1%g) by rewrite cfResE ?group1.
rewrite ['Res _]cfun_sum_cfdot sum_cfunE.
elim/big_ind: _ => [||i _]; [exact: dvdC0 | exact: dvdC_add | rewrite cfunE].
rewrite dvdC_mulr ?isIntC_Nat ?isNatC_irr1 //.
have [j ->]: exists j, 'chi_i = 'Res 'chi[G]_j.
  case/predU1P: ZHG => [-> | cGG] in i *.
    suffices ->: i = 0 by exists 0; rewrite !chi0_1 cfRes_cfun1 ?sub1G.
    apply/val_inj; case: i => [[|i] //=]; rewrite ltnNge NirrE.
    by rewrite (@leq_trans 1) // leqNgt classes_gt1 eqxx.
  have linG := char_abelianP G cGG; have linG1 j := eqP (proj2 (andP (linG j))).
  have /fin_all_exists[rH DrH] j: exists k, 'Res[H, G] 'chi_j = 'chi_k.
    apply/irrP/lin_char_irr/andP.
    by rewrite cfRes_char ?irr_char // cfRes1 ?linG1.
  suffices{i} all_rH: codom rH =i Iirr H.
    by exists (iinv (all_rH i)); rewrite DrH f_iinv.
  apply/subset_cardP; last exact/subsetP; apply/esym/eqP.
  rewrite card_Iirr_abelian ?(abelianS sHG) //.
  rewrite -(eqn_pmul2r (indexg_gt0 G H)) Lagrange //; apply/eqP.
  rewrite -sum_nat_const -card_Iirr_abelian // -sum1_card.
  rewrite (partition_big rH (mem (codom rH))) /=; last exact: image_f.
  have nsHG: H <| G by rewrite -sub_abelian_normal.
  apply: eq_bigr => _ /imageP[i _ ->]; rewrite -card_quotient ?normal_norm //.
  rewrite -card_Iirr_abelian ?quotient_abelian //.
  have Mlin j1 j2: exists k, 'chi_j1 * 'chi_j2 = 'chi[G]_k.
    apply/irrP/lin_char_irr/andP.
    by rewrite cfunE !linG1 mulr1 mul_char ?irr_char.
  have /fin_all_exists[rQ DrQ] (j : Iirr (G / H)) := Mlin i (mod_Iirr j).
  have mulJi: ('chi[G]_i)^*%CF * 'chi_i = 1.
    apply/cfun_inP=> x Gx; rewrite !cfunE -lin_charV_conj ?linG // cfun1E Gx.
    by rewrite lin_charV ?mulVf ?lin_char_neq0 ?linG.
  have inj_rQ: injective rQ.
    move=> j1 j2 /(congr1 (fun k => (('chi_i)^*%CF * 'chi_k) / H)%CF).
    by rewrite -!DrQ !mulrA mulJi !mul1r !mod_IirrE ?cfModK // => /chi_inj.
  rewrite -(card_imset _ inj_rQ) -sum1_card; apply: eq_bigl => j.
  rewrite -(inj_eq chi_inj) -!DrH; apply/eqP/imsetP=> [eq_ij | [k _ ->]].
    have [k Dk] := Mlin (conjC_Iirr i) j; exists (quo_Iirr H k) => //.
    apply/chi_inj; rewrite -DrQ quo_IirrK //.
      by rewrite -Dk conjC_IirrE mulrCA mulrA mulJi mul1r.
    apply/subsetP=> x Hx; have Gx := subsetP sHG x Hx.
    rewrite cfker_irrE inE linG1 -Dk conjC_IirrE; apply/eqP.
    transitivity ((1 : 'CF(G)) x); last by rewrite cfun1E Gx.
    by rewrite -mulJi !cfunE -!(cfResE _ sHG Hx) eq_ij.
  rewrite -DrQ; apply/cfun_inP=> x Hx; rewrite !cfResE // cfunE mulrC.
  by rewrite cfker1 ?linG1 ?mul1r ?(subsetP _ x Hx) // mod_IirrE ?cfker_Mod.
have: dvdNC #|G : H| (#|G : H|%:R * '[chi, 'chi_j]).
  by rewrite dvdC_mulr ?isIntC_Nat ?cfdot_char_irr_Nat.
congr (dvdNC _ _); rewrite (cfdotEl _ Hchi) -(Lagrange sHG) mulnC natrM.
rewrite invfM -mulrA mulVKf ?neq0GiC //; congr (_ * _).
by apply: eq_bigr => x Hx; rewrite !cfResE.
Qed.

(* This is Isaacs, Theorem (3.13). *)
Theorem faithful_degree_p_part gT (p : nat) (G P : {group gT}) i :
    cfaithful 'chi[G]_i -> p.-nat (getNatC ('chi_i 1%g)) ->
    p.-Sylow(G) P -> abelian P ->
  'chi_i 1%g = (#|G : 'Z(G)|`_p)%N%:R.
Proof.
have [p_pr | pr'p] := boolP (prime p); last first.
  have p'n n: (n > 0)%N -> p^'.-nat n.
    by move/p'natEpi->; rewrite mem_primes (negPf pr'p).
  rewrite irr1_degree getNatC_nat => _ /pnat_1-> => [_ _|].
    by rewrite part_p'nat ?p'n.
  by rewrite p'n ?irr_degree_gt0.
move=> fful_i /p_natP[a Dchi1] sylP cPP.
have Dchi1C: 'chi_i 1%g = (p ^ a)%:R.
  by rewrite -Dchi1 irr1_degree getNatC_nat.
have pa_dv_ZiG: (p ^ a %| #|G : 'Z(G)|)%N.
  rewrite -dvdC_nat -Dchi1C -(cfcenter_fful_irr fful_i).
  exact: dvd_irr1_index_center.
have [sPG pP p'PiG] := and3P sylP.
have ZchiP: 'Res[P] 'chi_i \in 'CF(P, P :&: 'Z(G)).
  apply/cfun_onP=> x; rewrite inE; have [Px | /cfun0->//] := boolP (x \in P).
  rewrite /= -(cfcenter_fful_irr fful_i) cfResE //.
  apply: coprime_degree_support_cfcenter.
  rewrite Dchi1 coprime_expl // prime_coprime // -p'natE //.
  apply: pnat_dvd p'PiG; rewrite -index_cent1 indexgS // subsetI sPG.
  by rewrite sub_cent1 (subsetP cPP).
have /andP[_ nZG] := center_normal G; have nZP := subset_trans sPG nZG.
apply/eqP; rewrite Dchi1C -eqN_eqC eqn_dvd -{1}(pfactorK a p_pr) -p_part.
rewrite partn_dvd //= -dvdC_nat -Dchi1C -card_quotient //=.
rewrite -(card_Hall (quotient_pHall nZP sylP)) card_quotient // -indexgI.
rewrite -(cfResE _ sPG) // index_support_dvd_degree ?subsetIl ?cPP ?orbT //.
by rewrite cfRes_char ?irr_char.
Qed.

End MoreIntegralChar.