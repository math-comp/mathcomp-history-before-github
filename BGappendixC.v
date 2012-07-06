(* (c) Copyright Microsoft Corporation and Inria. All rights reserved.        *)
Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat div prime seq.
Require Import tuple fintype finfun ssralg finalg finset bigop.
Require Import fingroup cyclic morphism abelian frobenius zmodp gproduct.
Require Import polydiv poly vector vector falgebra fieldext galois finfield.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope group_scope.
Open Local Scope ring_scope.
Import GRing.Theory.
Import FinRing.Theory.

Lemma linear_root (F : fieldType) (p : {poly F}) : size p = 2 -> {r | root p r}.
Proof.
move => size_p.
have := lead_coefE p.
rewrite size_p [_.-1]/= => Hlead.
exists ((- p`_0) / lead_coef p).
rewrite rootE horner_coef size_p.
rewrite !big_ord_recl big_ord0 expr0 mulr1 expr1.
rewrite mulrC.
rewrite Hlead mulfVK ?addr0 ?subrr //.
by rewrite -Hlead lead_coef_eq0 -size_poly_eq0 size_p.
Qed.

Lemma cubic_root (F : fieldType) (p q : {poly F}) :
  size p <= 4 -> 1 < size q < size p -> q %| p -> {r | root p r}.
Proof.
move => size_p /andP [size_q size_qp] Hqp.
case: (@eqP _ (size q) 2) => [/linear_root [r Hr]|size_q_neq_2].
  by exists r; rewrite -dvdp_XsubCl (dvdp_trans _ Hqp) // dvdp_XsubCl.
pose qq := p %/ q.
have Hqqp : qq %| p by rewrite -(divpK Hqp) dvdp_mulIl.
suff/linear_root : size qq = 2 => [[r Hr]|].
  by exists r; rewrite -dvdp_XsubCl (dvdp_trans _ Hqqp) // dvdp_XsubCl.
rewrite size_divp; last by rewrite -size_poly_eq0 -(ltn_predK size_q).
move: (size q) (size p) size_p size_q size_qp size_q_neq_2.
by do 3 case => //; move => szq; do 5 case => //; case: szq.
Qed.

Lemma cubicNroot (F : fieldType) (p : {poly F}) :
  1 < size p <= 4 -> (forall r, ~~ root p r) -> irreducible_poly p.
Proof.
move/andP => [size_p1 size_p4] Hp.
split => [|q size_q Hqp]; first done.
rewrite -(dvdp_size_eqp Hqp).
have Hp0 : p != 0 by rewrite -size_poly_eq0 -lt0n -ltnS leqW.
have := (dvdp_leq Hp0 Hqp).
rewrite leq_eqVlt.
case/orP => [//|Hqp_size].
have size_q1: 1 < size q.
  case: (size q) size_q Hqp (size_poly_eq0 q) Hp0 => [_|[//|//]].
  rewrite eqxx.
  case: eqP => [->|//].
  by rewrite dvd0p => ->.
have /andP/(cubic_root size_p4)/(_ Hqp) [r Hr] := (conj size_q1 Hqp_size).
have := Hp r.
by rewrite Hr.
Qed.

Lemma coprimep_map (F : fieldType) (rR : idomainType) (f : {rmorphism F -> rR})
    (p q : {poly F}) : coprimep (map_poly f p) (map_poly f q) = coprimep p q.
Proof.
rewrite -gcdp_eqp1 -gcdp_map -(rmorph1 [rmorphism of map_poly f]).
by rewrite eqp_map gcdp_eqp1.
Qed.

Section AppendixC.

Variables p q : nat.
Hypothesis p_prime : prime p.
(*Hypothesis q_prime : prime q. *)
Hypothesis Hpq : ~~ (q %| p.-1)%N.

Variable gT : finGroupType.
Variables H P U : {group gT}.
Hypothesis HfrobHPU : [Frobenius H = P ><| U].
Hypothesis Pcard : #|P| = (p ^ q)%N.
Hypothesis Ucard : (#|U| * p.-1)%N = (p ^ q).-1.
Hypothesis HCUP : 'C_U(P) = 1%g.

Variable Q : {group gT}.
Hypothesis HQ : q.-abelem Q.

Variable P0 : {group gT}. 
Hypothesis HP0P : P0 \subset P.
Hypothesis HP0Q : P0 \subset 'N(Q).

Variable y : gT.
Hypothesis HyQ : y \in Q.
Hypothesis HP0Uy : P0 \subset 'N(U :^ y).

CoInductive finFieldImage : Type :=
  FinFieldImage (F : finFieldType) (sigma : {morphism P >-> F})
                (psi : gT -> F) (_ : isom P [set: F] sigma)
                (_ : {in P & U, forall s u, sigma (s ^ u) = psi u * sigma s}).

Variable FSigmaPsi : finFieldImage.

Let F : finFieldType :=
  let: FinFieldImage F _ _ _ _ := FSigmaPsi in F.

Let sigma : {morphism P >-> F} :=
  let (_,sigma,_,_,_) as FST
  return {morphism P >-> ((let: FinFieldImage F _ _ _ _ := FST in F)
                          : finFieldType)}
  := FSigmaPsi in sigma.

Let Fp := <[(1%R : F)]>.

Hypothesis HP0Fp : sigma @: P0 = Fp.

Let Hsigma : isom P [set: F] sigma.
Proof. by rewrite /sigma /F; case: FSigmaPsi. Qed.

Let Pconj : {in P & U, forall s u, s ^ u \in P}.
Proof.
move => s u Hs Hu.
rewrite /= memJ_norm //.
case/Frobenius_context: HfrobHPU => /sdprodm_norm/subsetP HPU _ _ _ _.
by apply: HPU.
Qed.

Let psi : gT -> F :=
  let (_,_,psi,_,_) as FST
  return gT -> ((let: FinFieldImage F _ _ _ _ := FST in F) : finFieldType)
  := FSigmaPsi in psi.

Let Hpsi : {in P & U,  forall s u, sigma (s ^ u) = psi u * sigma s}.
Proof. by rewrite /sigma /psi /F; case: FSigmaPsi. Qed.

Let Fcard : #|F| = (p ^ q)%N.
Proof. by rewrite -Pcard (isom_card Hsigma) cardsT. Qed.

Let q_neq0 : q != 0%N.
Proof.
(*Replace this once we decide we need to assume q_prime *)
(*by rewrite -lt0n prime_gt0. *)
move/eqP: Fcard.
apply: contraTneq => ->.
by rewrite expn0 neq_ltn finRing_card_gt1 orbT.
Qed.

Let Fchar : finChar F = p.
Proof.
rewrite /finChar Fcard.
move: q_neq0; rewrite -lt0n; move/prednK <-.
by rewrite pdiv_pfactor.
Qed.

Let sfF : splittingFieldType _ := [splittingFieldType _ of primeFieldExtType F].

Let Fdim : \dim {:sfF} = q.
Proof.
rewrite primeFieldExt_dimf.
have /expnI : 1 < finChar F by rewrite prime_gt1 // finChar_prime.
apply.
by rewrite -finField_card [X in (X ^ _)%N]Fchar -Fcard.
Qed.

Let s := isom_inv Hsigma 1%R.

Let sigma_s : sigma s = 1.
Proof. by rewrite invmK // (isom_im Hsigma) inE. Qed.

Let s_P0 : s \in P0.
Proof.
rewrite /s.
have : 1 \in Fp by apply: cycle_id.
rewrite -HP0Fp.
case/imsetP => s' Hs' ->.
have Hs'P : s' \in P by apply: (subsetP HP0P).
by rewrite [isom_inv _ _]invmE //.
Qed.

Let s_P : s \in P.
Proof. by apply: (subsetP HP0P). Qed.

Let s_neq_1 : s != 1%g.
Proof.
rewrite -(can_in_eq (invmE (isom_inj Hsigma))) ?group1 //.
by rewrite morph1 sigma_s oner_neq0.
Qed.

Local Notation "`| x |" := (galNorm 1 {:sfF} x).

Let E := [set x : sfF | `| x | == 1 & `| 2%:R - x | == 1].

Let E_nontriv : 1 \in E.
Proof. by rewrite !inE -addrA subrr addr0 galNorm1 eqxx. Qed.

Let two_minus_E x : (x \in E) = (2%:R - x \in E).
Proof. by rewrite !inE opprB addrA [2%:R + x]addrC addrK andbC. Qed.

Let psiE : {in U, forall u, psi u = sigma (s ^ u)}.
Proof. by move => u Hu; have -> := Hpsi s_P Hu; rewrite sigma_s mulr1. Qed.

Lemma psiU_galois_norm_1_subproof : psi @: U = [set x : sfF | `| x | == 1].
Proof.
pose psi' x0 := odflt (1%g : {unit F}) (insub (psi x0)).
have psi'E : {in U, forall u, val (psi' u) = psi u}.
  move => u Hu; rewrite /psi'.
  case: insubP => [//|].
  rewrite psiE // unitfE.
  rewrite morph_injm_eq1 ?(isom_inj Hsigma) ?conjg_eq1 ?s_neq_1 // memJ_norm //.
  case: (Frobenius_context HfrobHPU) => /sdprodP [_ _ /subsetP HUP _] _ _ _ _.
  by apply: HUP.
have <- : val @: (psi' @: U) = psi @: U.
  by rewrite -imset_comp; apply: eq_in_imset; apply: psi'E.
pose N1 := [set x : {unit F} | `| val x | == 1].
have -> : [set x | `| x | == 1] = val @: N1.
  apply/setP => a; rewrite !inE.
  apply/idP/imsetP; last by case => b; rewrite inE => ? ->.
  move => Ha.
  have a_unit : a \is a GRing.unit.
    by rewrite unitfE -(galNorm_eq0 1 {:sfF}) (eqP Ha) oner_neq0.
  exists (FinRing.unit _ a_unit); last by rewrite SubK.
  by rewrite /= ?inE SubK.
suff /eqP -> : psi' @: U == N1 by done.
have N1G : group_set N1.
  apply/group_setP; split => [|a b /=].
    by rewrite inE val_unit1 galNorm1.
  rewrite !inE => /eqP Ha Hb.
  by rewrite galNormM Ha mul1r.
(* Maybe it would be better to show that psi' is a morphism *)
have psi'UG : group_set (psi' @: U).
  apply/group_setP; split => [|_ _ /imsetP [a Ha ->] /imsetP [b Hb ->]].
    apply/imsetP; exists 1%g; first by apply: group1.
    by apply: val_inj; rewrite psi'E // psiE // conjg1 sigma_s.
  have Hab := groupM Ha Hb.
  apply/imsetP; exists (a * b)%g; first done.
  apply: val_inj.
  symmetry.
  by rewrite val_unitM !psi'E // psiE // conjgM Hpsi ?Pconj // mulrC -psiE.
rewrite (@eq_subG_cyclic _ [set: {unit F}] (group psi'UG) (group N1G))
        ?subsetT ?field_unit_group_cyclic //=.
rewrite card_in_imset; last first.
  move => u v Hu Hv /(f_equal val).
  rewrite !psi'E // => Huv.
  case/isomP: Hsigma => /injmP => sigma_inj _.
  have HPuv : {in P, forall s', s' ^ u = s' ^ v}.
    move => s' Hs'; apply: sigma_inj; try apply: Pconj => //.
    by rewrite !Hpsi // Huv.
  apply/eqP; rewrite eq_mulgV1; apply/eqP/set1gP; rewrite -HCUP.
  rewrite inE groupM ?groupV //=.
  apply/cent_classP/setP => a.
  rewrite inE.
  apply/idP/eqP; last by move ->; apply: class_refl.
  case/imsetP => b Hb ->.
  rewrite conjgE.
  apply: (canF_LR (mulKVg _)).
  apply: (canF_LR (mulKg _)).
  rewrite -conjgE.
  rewrite conjgM.
  apply: (canF_RL (conjgKV _)).
  by rewrite HPuv.
have Hp1 : 0 < p.-1.
  have /subnK <- := prime_gt1 p_prime.
  by rewrite addn2.
rewrite -(eqn_pmul2r Hp1) Ucard.
have [x Hgen Hx] := finField_galois_generator (sub1v {:sfF}).
pose f (x : {unit F}) := (x ^+ (p ^ q - p))%g.
have f_morph : {in [set: {unit F}] &, {morph f : x y / (x * y)%g}}.
  move => a b /=.
  rewrite /f expgMn //.
  apply: val_inj.
  by rewrite !val_unitM mulrC.
have -> : N1 = Morphism f_morph @* [set: {unit F}].
  rewrite morphimEdom.
  apply/setP => a.
  rewrite !inE.
  apply/(hilbert's_theorem_90 Hgen (memvf _))/imsetP.
    case => b [_]; rewrite -unitfE => Hb Hab.
    exists (FinRing.unit _ Hb); first by rewrite inE.
    apply: val_inj.
    rewrite Hab val_unitX Hx ?memvf //=.
    rewrite dimv1 expn1.
    rewrite card_Fp ?finChar_prime //.
    rewrite [X in _ ^+ X]Fchar.
    rewrite -[X in X / _]finField_expf_card /=.
    rewrite Fcard.
    apply: (canLR (mulrK _)); first by rewrite unitrX.
    rewrite -exprD subnK //.
    rewrite -[X in X <= _]expn1.
    rewrite leq_pexp2l //; first by rewrite prime_gt0.
    by rewrite lt0n.
  case => b _ Hab.
  exists (val b); first by apply/andP; rewrite memvf -unitfE; apply: valP.
  rewrite Hx ?memvf // dimv1 expn1.
  rewrite card_Fp ?finChar_prime // [X in _ ^+ X]Fchar.
  rewrite -val_unitX.
  apply: (canRL (mulrK _)); first by apply: valP.
  rewrite Hab -val_unitM.
  rewrite -expgD val_unitX.
  rewrite subnK; first by rewrite -Fcard finField_expf_card.
  rewrite -[X in X <= _]expn1.
  rewrite leq_pexp2l //; first by rewrite prime_gt0.
  by rewrite lt0n.
rewrite quotient.card_morphim.
rewrite setIid.
rewrite mulnC.
suff -> : p.-1 = #|('ker (Morphism f_morph))%G|.
  by rewrite Lagrange ?subsetT // finField_unit_card Fcard.
rewrite -Fchar.
rewrite -[X in X.-1]card_Fp ?finChar_prime //.
have /card_imset <- : injective (in_alg sfF) by apply: fmorph_inj.
set S := _ @: _.
have /setD1K <- : 0 \in S.
  apply/imsetP.
  exists 0; first by rewrite inE.
  by rewrite rmorph0.
rewrite cardsU1.
rewrite setD11 add1n /=.
rewrite -(card_imset _ (val_inj)) .
suff <-: [set val x | x : {unit F} in 'ker (Morphism f_morph)] = S :\ 0 by done.
apply/setP => a.
rewrite !inE.
apply/imsetP/andP.
  case => b Hb ->.
  split; first by rewrite -unitfE; apply: valP.
  move: Hb.
  rewrite kerE.
  rewrite morphpreE.
  rewrite setTI.
  rewrite inE /= /f.
  move/set1P/eqP.
  rewrite -(can_eq (mulgK (b ^+ p)%g)).
  rewrite mul1g.
  rewrite -expgD.
  rewrite subnK; last first.
    rewrite -[X in X <= _]expn1.
    rewrite leq_pexp2l //; first by rewrite prime_gt0.
    by rewrite lt0n.
  rewrite -Fcard.
  rewrite -(inj_eq val_inj).
  rewrite !val_unitX.
  rewrite finField_expf_card.
  rewrite eq_sym.
  rewrite -Fchar.
  rewrite -[X in _ ^+ X]card_Fp ?finChar_prime //.
  rewrite -[X in _ ^+ X]expn1.
  rewrite -[X in (_ ^ X)%N](dimv1 sfF).
  rewrite -(fermat's_little_theorem 1 (val b : sfF)).
  case/vlineP => k ->.
  apply: mem_imset.
  by rewrite inE.
rewrite -unitfE.
case => a_unit HaS.
exists (FinRing.unit _ a_unit); last done.
rewrite kerE morphpreE setTI inE /= /f.
apply/set1P.
apply/val_inj.
rewrite val_unitX /=.
apply/(can_inj (mulrK (unitrX p a_unit))).
rewrite -exprD.
rewrite mul1r.
rewrite subnK; last first.
  rewrite -[X in X <= _]expn1.
  rewrite leq_pexp2l //; first by rewrite prime_gt0.
  by rewrite lt0n.
rewrite -Fcard.
rewrite finField_expf_card.
case/imsetP: HaS => k Hk ->.
rewrite -rmorphX.
rewrite -Fchar.
rewrite -[X in _ ^+ X]card_Fp ?finChar_prime //.
by rewrite finField_expf_card.
Qed.

Lemma BG_appendix_C1 : E = [set x^-1 | x in E] -> 1 < #|E| -> p <= q.
Proof.
move => HEinv.
rewrite (cardsD1 1) E_nontriv add1n ltnS card_gt0.
case/set0Pn => /= a.
rewrite 2!inE => /andP [Ha1 HaE].
pose tau (b : F) := (2%:R - b)^-1.
have HtauE b : b \in E -> tau b \in E.
  rewrite /tau two_minus_E => Hb.
  by rewrite HEinv; apply: mem_imset.
pose tauk k (b : F) := (k%:R - (k%:R - 1) * b) / (k%:R + 1 - k%:R * b).
have Htauk k : tauk k a \in E.
  elim: k {Ha1} a HaE => [|k IH] b HbE.
    by rewrite /tauk !add0r !mul0r !subr0 divr1 mulN1r opprK.
  have H2b0 : (2%:R - b) != 0.
    rewrite -(galNorm_eq0 1 {:sfF}).
    move: HbE.
    rewrite inE => /andP [_ /eqP ->].
    by apply: oner_neq0.
  move/HtauE/IH: HbE.
  rewrite /tauk /tau [k.+1%:R]mulrSr addrK.
  rewrite -[X in (X - _) / _](mulfK H2b0) -mulrBl.
  rewrite -[X in _ / (X - _)](mulfK H2b0) -mulrBl.
  rewrite [X in (_ / X)]mulrC invfM mulrA invrK mulfVK //.
  have -> : (k%:R * (2%:R - b) - (k%:R - 1)) = (k%:R + 1 - k%:R * b).
    rewrite mulrBr opprB addrC addrA; congr (_ - _).
    by rewrite mulr2n mulrDr mulr1 addrA subrK addrC.
  suff -> : ((k%:R + 1) * (2%:R - b) - k%:R) = (k%:R + 1 + 1 - (k%:R + 1) * b).
    done.
  rewrite mulrDr mulrN -[X in X = _]addrA [_ - _]addrC addrA; congr (_ - _).
  rewrite [X in X * _]addrC mulr2n mulrDr mulr1 addrA addrK.
  by rewrite [X in X + _]addrC.
pose Gal := 'Gal({:sfF} / 1).
pose galPoly := \prod_(x in Gal) (x (1 - a) *: 'X + 1).
have galPoly_roots :
  all (root (galPoly - 1)) [seq in_alg sfF x | x <- (enum 'F_(finChar F))].
  apply/allP => _ /mapP [k _ ->].
  rewrite rootE !hornerE horner_prod subr_eq0 /=.
  rewrite -[X in X%:A]valZpK -Zp_nat -scalerMnl scale1r.
  apply/eqP.
  pose prod_tau_inv := \prod_(i < k)
    ((i.+1%:R - (i.+1%:R - 1) * a)^-1 / (i.+1%:R + 1 - i.+1%:R * a)^-1).
  apply: (eq_trans (y:= `|prod_tau_inv|)); last first.
    rewrite galNorm_prod.
    apply: big1 => i _.
    have := Htauk i.+1.
    rewrite inE -invfM galNormV.
    by case/andP => /eqP ->; rewrite invr1.
  have -> : prod_tau_inv = (k%:R + 1) - k%:R * a.
    rewrite /prod_tau_inv {prod_tau_inv}.
    case: {k} (k : nat) => [|k]; first by rewrite big_ord0 add0r mul0r subr0.
    rewrite big_split big_ord_recl big_ord_recr /=.
    rewrite subrr mul0r subr0 invr1 mul1r invrK.
    rewrite mulrA -big_split /= big1 ?mul1r // => i _.
    rewrite -(@natrD _ (i.+1) 1) addnC (@natrB _ i.+2 1) // divff // invr_eq0.
    move: (Htauk (bump 0 i).+1) (oner_neq0 F).
    rewrite inE; case/andP.
    rewrite galNormM => /eqP Hgal _.
    rewrite -[X in X != _]Hgal mulf_eq0 negb_or (@galNorm_eq0 _ sfF).
    by case/andP.
  have -> : (k%:R + 1) - k%:R * a = (1 - a) * k%:R + 1.
    by rewrite addrC addrA [X in X + _]addrC mulrC mulrBl mul1r.
  apply: eq_bigr => i Hi.
  symmetry.
  by rewrite !hornerE rmorphD rmorphM rmorphMn rmorph1.
rewrite -ltnS.
have size_galPoly : size galPoly = q.+1.
  have Hfactor (x : {rmorphism F -> F}) : size (x (1 - a) *: 'X + 1) = 2.
    rewrite -mul_polyC size_MXaddC (negbTE (oner_neq0 _)) andbF.
    by rewrite size_polyC fmorph_eq0 subr_eq0 eq_sym (negbTE Ha1).
  rewrite size_prod; last first.
    by move => i _; rewrite -size_poly_eq0 (Hfactor [rmorphism of i]).
  set S := (\sum_(i in Gal) _)%N.
  have -> : S = (\sum_(i in Gal) 2)%N.
    by apply: eq_bigr => i _; apply: (Hfactor [rmorphism of i]).
  rewrite sum_nat_const -add1n mulnC !addnA addn0 addnK add1n.
  have /galois_dim <- := finField_galois (sub1v {:sfF}).
  by rewrite dimv1 divn1 Fdim.
have size_galPoly1 : size (galPoly - 1) = q.+1.
  by rewrite size_addl // size_opp size_poly1 size_galPoly ltnS lt0n.
rewrite -size_galPoly1.
have galPoly1_neq0 : galPoly - 1 != 0.
  by rewrite -size_poly_eq0 size_galPoly1.
rewrite -[p]card_Fp // -Fchar cardE -(size_map (in_alg sfF)).
apply: max_poly_roots => //.
rewrite map_inj_uniq ?enum_uniq //.
by apply: fmorph_inj.
Qed.

Lemma BG_appendix_C2b : q = 3 -> 1 < #|E|.
Proof.
move => Hq3.
rewrite (cardsD1 1) E_nontriv add1n ltnS card_gt0.
apply/set0Pn => /=.
pose f' (c : 'F_(finChar F)) := 'X * ('X - 2%:R%:P) * ('X - c%:P) + ('X - 1).
pose f c := map_poly (in_alg sfF) (f' c).
have /= Hf0 c : ~~ root (f' c) 0 by rewrite /root !hornerE oppr_eq0 oner_eq0.
have /= Hf2 c : ~~ root (f' c) 2%:R.
  by rewrite /root !(hornerE, subrr) /= addrK oner_neq0.
have /= Hf_root a b d : root (f a) d -> root (f b) d -> a = b.
  move => Hfa Hfb.
  have Hd_neq0 : d != 0.
    apply: contraNneq (Hf0 a).
    by rewrite -(fmorph_root [rmorphism of (in_alg sfF)]) rmorph0 => <-.
  have Hd_neq2 : (d - 2%:R) != 0.
    apply: contra (Hf2 a).
    rewrite subr_eq0 -(fmorph_root [rmorphism of (in_alg sfF)]).
    by rewrite rmorphMn rmorph1 => /eqP <-.
  move: Hfb Hfa; rewrite /root => /eqP <-.
  rewrite /f ![map_poly _ _]rmorphD !rmorphM !rmorphB /=.
  rewrite !map_polyX !map_polyC /= -in_algE rmorphMn rmorph1 !hornerE /=.
  rewrite 2!(can_eq (addrK _)) -!mulrA.
  rewrite (can_eq (mulKf Hd_neq0)) (can_eq (mulKf Hd_neq2)).
  rewrite (can_eq (addKr _)) eqr_opp -!in_algE (inj_eq (fmorph_inj _)).
  by apply/eqP.
case: (boolP [forall c, exists d, root (f' c) d]).
  move/forallP => Hrootf.
  pose ch c := xchoose (existsP (Hrootf c)).
  suff [chinv chK chinvK] : bijective ch.
    move: (chinvK 0) (xchooseP (existsP (Hrootf (chinv 0)))) (Hf0 (chinv 0)).
    by rewrite /ch => -> ->.
  rewrite /ch.
  apply: injF_bij => a b Hab.
  apply: (Hf_root _ _ (xchoose (existsP (Hrootf a)))%:A).
    by rewrite fmorph_root; apply: (xchooseP (existsP (Hrootf _))).
  by rewrite Hab fmorph_root; apply: (xchooseP (existsP (Hrootf _))).
rewrite negb_forall => /existsP /= [c].
rewrite negb_exists => /forallP /= Hc.
have size_fcr :
  size ('X * ('X - (2%:R)%:P) * ('X - c%:P)) = 4.
  rewrite -mulrA mulrC size_mulX ?mulf_eq0 ?polyXsubC_eq0 //.
  by rewrite size_mul ?polyXsubC_eq0 // !size_XsubC.
have size_fc : size (f' c) = 4.
  by rewrite size_addl ?size_XsubC size_fcr.
have fc_monic : f' c \is monic.
  rewrite monicE lead_coefDl ?size_XsubC ?size_fcr //.
  by rewrite -monicE !monicMl ?monicXsubC ?monicX.
have {size_fcr} fc_irr : irreducible_poly (f' c).
  by apply: cubicNroot; first rewrite size_fc.
suff /existsP [a Ha] : [exists a, root (f c) a].
  have fc_over1 : f c \is a polyOver 1%AS.
    by apply/polyOverP => i; rewrite coef_map /= memvZ // mem1v.
  have /eqP fc_min : minPoly 1 a == f c.
    rewrite -eqp_monic ?monic_minPoly ?monic_map //.
    have := minPoly_dvdp fc_over1 Ha.
    have := size_minPoly 1 a.
    suff [r <-] : {r | map_poly (in_alg sfF) r = minPoly 1 a}.
      rewrite size_map_poly dvdp_map eqp_map => Hsize.
      by apply: fc_irr; rewrite Hsize.
    move: (minPoly 1 a) (minPolyOver 1 a) => r /polyOverP Hr.
    exists (\poly_(i < size r) coord [tuple 1] 0 r`_i).
    apply/polyP => i; rewrite coef_map coef_poly.
    case: leqP => [/leq_sizeP/(_ _ (leqnn i)) ->|]; first by rewrite /= scale0r.
    move => _; symmetry.
    have : r`_i \in <<[tuple 1%R]>>%VS by rewrite span_seq1.
    by move/coord_span; rewrite big_ord1.
  have Hgalois := finField_galois (sub1v {:sfF}).
  have card_gal : #|'Gal({:sfF} / 1)| = 3.
    by rewrite -(galois_dim Hgalois) dimv1 divn1 Fdim.
  have fc_factor : f c = \prod_(x in 'Gal({:sfF} / 1)) ('X - (x a)%:P).
    rewrite -fc_min.
    have : size (minPoly 1 a) = (\dim_(1%AS : {vspace sfF}) {:sfF}).+1.
      by rewrite fc_min size_map_poly size_fc dimv1 divn1 Fdim Hq3.
    have/galois_factors [_] := Hgalois.
    case/(_ _ (memvf a)) => r [Hr /map_uniq Hr_uniq ->].
    rewrite big_map size_prod_XsubC big_uniq //=.
    case => size_r.
    move/card_uniqP: Hr_uniq; rewrite size_r (galois_dim Hgalois) => card_r.
    apply: eq_bigl.
    by apply/(subset_cardP card_r).
  exists a; rewrite !inE; apply/and3P; split.
  - apply: contraTneq Ha => ->.
    by rewrite -[1]scale1r fmorph_root; apply Hc.
  - rewrite -eqr_opp; apply/eqP.
    have -> : -1 = (f c).[in_alg _ 0].
      by rewrite horner_map !hornerE rmorphN rmorph1.
    rewrite rmorph0 -mulN1r.
    have -> : -1 = (-1) ^+ #|'Gal({:sfF} / 1)| :> F.
      by rewrite card_gal -signr_odd expr1.
    rewrite -prodrN fc_factor horner_prod.
    by apply: eq_bigr => i _; rewrite !hornerE.
  - apply/eqP.
    transitivity (f c).[in_alg _ 2%:R]; last first.
      by rewrite horner_map !hornerE /= subrr mulr0 mul0r add0r addrK scale1r.
    rewrite fc_factor horner_prod.
    by apply: eq_bigr => i _; rewrite rmorphB !rmorphMn !rmorph1 !hornerE.
suff : ~~ coprimep (f' c) ('X ^+ #|F| - 'X).
  apply: contraR; rewrite negb_exists => /forallP Hroot.
  rewrite -(coprimep_map [rmorphism of (in_alg sfF)]) -gcdp_eqp1.
  rewrite rmorphB /= map_polyXn map_polyX finField_genPoly.
  have /dvdp_prod_XsubC [m Hm] := dvdp_gcdr (f c) (\prod_x ('X - x%:P)).
  apply: (eqp_trans Hm).
  rewrite /eqp dvd1p andbT.
  apply uniq_roots_dvdp; last first.
    by rewrite uniq_rootsE mask_uniq // /index_enum /= -enumT enum_uniq.
  apply/allP => x.
  rewrite -root_prod_XsubC -(eqp_root Hm) root_gcd.
  by rewrite -[root (f c) x]negbK Hroot.
case/irredp_FAdjoin: fc_irr => L dimL [z Hz H1z].
rewrite size_fc /= in dimL.
rewrite -(coprimep_map [rmorphism of (in_alg L)]).
rewrite rmorphB /= map_polyXn map_polyX.
move: (map_poly _ _) Hz => r root_r.
suff: ('X^#|F| - 'X).[z] == 0.
  apply: contraL => Hcoprime.
  by apply: (coprimep_root Hcoprime).
move: Fdim; rewrite finField_card dimvf /Vector.dim /= => ->.
rewrite !(hornerE, hornerXn) subr_eq0 Hq3 -dimL.
rewrite -[X in (X ^ _)%N]card_Fp ?finChar_prime //.
by rewrite -fermat's_little_theorem memvf.
Qed.

Let t := s ^ y.

Let P1 := P0 :^ y.

Local Open Scope group_scope.
(*
Lemma BG_appendix_C3_1 x : x \in H ->
  exists u, exists v, exists s1, 
  [/\ u \in U, v \in U, s1 \in P0 & x = u * s1 * v].
Proof.
case/Frobenius_context: HfrobHPU => HPUH _ _ _ _.
case/(mem_sdprod HPUH) => s' [u' [Hs' Hu' -> Hs'u']].
case: (eqVneq s' 1) => Hs1.
  exists u'; exists 1; exists 1.
  by split => //; rewrite !mulg1 Hs1 mul1g.
*)
(* Lemma BG_appendix_C : p <= q. *)

End AppendixC.
