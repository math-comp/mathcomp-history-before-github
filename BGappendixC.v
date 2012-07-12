(* (c) Copyright Microsoft Corporation and Inria. All rights reserved.        *)
Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat div prime seq.
Require Import tuple fintype finfun ssralg finalg finset bigop fingroup.
Require Import quotient cyclic morphism abelian frobenius zmodp gproduct.
Require Import binomial commutator pgroup.
Require Import polydiv poly vector vector falgebra fieldext galois finfield.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope group_scope.
Open Local Scope ring_scope.
Import GRing.Theory.
Import FinRing.Theory.

Lemma modn_summ (I : Type) (r : seq I) (P : pred I) (F : I -> nat) d :
  \sum_(i <- r | P i) F i %% d = \sum_(i <- r | P i) F i %[mod d].
Proof.
apply/eqP.
elim: r => [|a r IH]; first by rewrite !big_nil.
rewrite !big_cons.
case: ifP => _ //.
by rewrite modnDml eqn_modDl.
Qed.

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
Hypothesis Hpq : ~~ (q %| p.-1)%N.

Variable gT : finGroupType.
Variables H P U : {group gT}.
Hypothesis HfrobHPU : [Frobenius H = P ><| U].
Hypothesis Pcard : #|P| = (p ^ q)%N.
Hypothesis Ucard : #|U| = ((p ^ q).-1 %/ p.-1)%N.

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

Let Fpis1 : Fp =i (1%VS : {vspace sfF}).
Proof.
move => x.
apply/cycleP/vlineP.
  case => i ->; exists (i%:R).
  by rewrite zmodXgE scaler_nat.
case => k ->; exists k.
by rewrite zmodXgE -(rmorph_nat [rmorphism of in_alg sfF]) natr_Zp.
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

Let PU_conj : {in P & U, forall s' u, s' ^ u \in P}.
Proof.
move => s' u Hs' Hu /=.
rewrite memJ_norm //.
case: (Frobenius_context HfrobHPU) => /sdprodP [_ _ /subsetP HUP _] _ _ _ _.
by apply: HUP.
Qed.

Let psi u := odflt (1%g : {unit F}) (insub (sigma (s ^ u))).

Let Hpsi : {in P & U, forall s' u, sigma (s' ^ u) = val (psi u) * sigma s'}.
Proof.
move => s' u Hs' Hu /=.
move: sigma_s; rewrite /psi.
case: insubP => [_ _ -> //|].
  rewrite /sigma /F; case: FSigmaPsi => F0 sigma0 psi0 _ Hpsi0 sigma0_s.
  by rewrite !Hpsi0 // sigma0_s mulr1.
rewrite unitfE morph_injm_eq1 ?(isom_inj Hsigma) ?conjg_eq1 ?s_neq_1 //.
by apply: PU_conj.
Qed.

Let psiE : {in U, forall u, val (psi u) = sigma (s ^ u)}.
Proof. by move => u Hu /=; rewrite (Hpsi s_P) // sigma_s mulr1. Qed.

Let psi_morphM : {in U &, {morph psi : x y / (x * y)%g}}.
Proof.
move => u1 u2 Hu1 Hu2 /=.
apply: val_inj.
rewrite val_unitM psiE ?groupM // psiE // conjgM //.
rewrite Hpsi //; first by rewrite mulrC.
by apply: PU_conj.
Qed.

Canonical psi_morph := Morphism psi_morphM.

Lemma psi_injm_subproof : 'injm psi.
Proof.
apply/injmP => u v Hu Hv Huv.
case/isomP: Hsigma => /injmP => sigma_inj _.
apply/eqP; rewrite eq_mulgV1; apply/eqP/set1gP.
case: (Frobenius_context HfrobHPU) => _ HP1 _ HPH _.
rewrite -(cent_semiregular (Frobenius_reg_compl HfrobHPU) _ HP1); last done.
rewrite inE groupM ?groupV //=.
apply/bigcapP => i Hi.
rewrite cent1C.
apply/cent1P/commgP/conjg_fixP.
rewrite conjgM; apply (canLR (conjgK _)).
apply: sigma_inj; try apply: Pconj => //.
by rewrite !Hpsi // Huv.
Qed.

Let prime_unit (a : {unit 'F_(finChar F)}) : {unit F} :=
 FinRing.Unit _ (rmorph_unit [rmorphism of in_alg sfF] (valP a)).

Let prime_unit_morphM :
  {in [set: {unit 'F_(finChar F)}] &, {morph prime_unit : x y / (x * y)%g}}.
Proof.
move => a b Ha Hb /=.
apply/val_inj.
by rewrite /= -(rmorphM [rmorphism of in_alg sfF]).
Qed.

Canonical prime_unit_morph := Morphism prime_unit_morphM.

Let prime_unit_injm : 'injm prime_unit.
Proof.
apply/injmP => a b _ _ /(f_equal val) /= Hab.
apply/val_inj.
by apply/(fmorph_inj [rmorphism of in_alg sfF]).
Qed.

Lemma BG_appendix_C_q_prime_subproof : prime q.
Proof.
have [] := pgroup_pdiv (abelem_pgroup HQ) _; last done.
apply: contraNneq s_neq_1 => HQ1.
suff /subsetP/(_ _ s_P0) : P0 \subset 1%G by rewrite inE.
rewrite /= -(Frobenius_trivg_cent HfrobHPU).
rewrite subsetI HP0P.
apply/commG1P/trivgP.
case/Frobenius_context: HfrobHPU => HPUH _ _ _ _.
case/sdprod_context: HPUH => _ _ _ U_norm <-.
rewrite subsetI (subset_trans (commSg _ HP0P)) ?commg_subl //=.
rewrite commg_subr -[X in 'N(X)]conjsg1.
have := HyQ.
rewrite HQ1.
by move/set1P <-.
Qed.

Lemma BG_appendix_C_remark_VII :
  (val : {unit F} -> sfF) @: (psi @* U) = [set x : sfF | `| x | == 1].
Proof.
pose f0 (x : {unit F}) := (x * x ^- p)%g.
have f_morph : {in [set: {unit F}] &, {morph f0 : x y / (x * y)%g}}.
  move => a b _ _ /=.
  rewrite /f0 /= expgMn; last by apply: val_inj; rewrite /= mulrC.
  rewrite invMg mulgA -[X in (X * a ^- p)%g]mulgA -mulgA.
  apply: val_inj => /=.
  by rewrite !val_unitX /= [X in _ * X]mulrC !mulrA.
pose f := Morphism f_morph.
have -> : [set x : sfF | `| x | == 1] = FinRing.uval @: (f @* [set: {unit F}]).
  apply/setP => a.
  have [x x_gen] := finField_galois_generator (sub1v {:sfF}).
  rewrite inE dimv1 expn1 card_Fp ?finChar_prime // => Hx.
  rewrite morphimEdom -imset_comp.
  apply/(hilbert's_theorem_90 x_gen (memvf a))/imsetP.
    case => b; rewrite -unitfE; case => _ Hb0 Hab.
    exists (FinRing.unit _ Hb0); rewrite ?inE //=.
    by rewrite Hab Hx /f ?memvf //= -Fchar val_unitX.
  case => b _ ->.
  exists (val b); first by apply/andP; rewrite memvf -unitfE; apply: valP.
  by rewrite Hx /f ?memvf //= -Fchar val_unitX.
do 3! apply/f_equal; apply/eqP.
rewrite (eq_subG_cyclic (G:=[set: {unit F}]%G)) ?subsetT
        ?field_unit_group_cyclic //=.
apply/eqP.
have := psi_injm_subproof.
rewrite -card_im_injm /= => /eqP ->.
rewrite card_morphim setIid -divgS ?subsetT // finField_unit_card Fcard.
rewrite -(card_imset _ val_inj) /=.
suff -> : FinRing.uval @: 'ker f = 
          (in_alg sfF \o val) @: [set: {unit 'F_(finChar F)}] .
  rewrite card_imset.
    by rewrite finField_unit_card card_Fp ?finChar_prime // Fchar.
  apply: inj_comp; last by apply: val_inj.
  apply: (fmorph_inj [rmorphism of in_alg sfF]).
apply/setP => x.
apply/imsetP/imsetP; last first.
  case => a _ ->.
  exists (prime_unit a); last done.
  apply/kerP; first by rewrite inE.
  apply:(canLR (mulgK _)).
  rewrite mul1g.
  apply: val_inj.
  rewrite val_unitX /= -(rmorphX [rmorphism of in_alg sfF]) -Fchar.
  by rewrite -[X in _ ^+ X]card_Fp ?finChar_prime // finField_expf_card.
case => a /kerP; rewrite inE => /(_ isT)/(canRL (mulgKV _)).
rewrite mul1g => Ha Hx.
have /vlineP [k Hk] : (x : sfF) \in 1%VS.
  rewrite fermat's_little_theorem.
  rewrite dimv1 expn1 card_Fp ?finChar_prime // [X in _ ^+ X]Fchar.
  by rewrite Hx -val_unitX -Ha.
have Hk0 : k \is a GRing.unit.
  rewrite unitfE -(fmorph_unit [rmorphism of in_alg sfF]) /= -Hk Hx.
  apply: (valP a).
exists (FinRing.Unit _ Hk0); last done.
by rewrite inE.
Qed.

Lemma BG_appendix_C_remark_VIII :
  psi @* U \x prime_unit @* [set: {unit 'F_(finChar F)}] = [set : {unit F}].
Proof.
rewrite 2!morphimEdom.
have card_psiU : #|psi @: U| = ((p ^ q).-1 %/ p.-1)%N.
  by rewrite (card_in_imset (injmP _ psi_injm_subproof)) Ucard.
have card_Fp : #|prime_unit @: [set: {unit 'F_(finChar F)}]| = p.-1.
  rewrite (card_in_imset (injmP _ prime_unit_injm)).
  by rewrite finField_unit_card card_Fp ?finChar_prime // Fchar.
have Hcoprime :
    coprime #|psi @: U| #|prime_unit @: [set: {unit 'F_(finChar F)}]|.
  rewrite card_psiU card_Fp -coprime_modl.
  suff -> : ((p ^ q).-1 %/ p.-1) = q %[mod p.-1].
    by rewrite coprime_modl prime_coprime // BG_appendix_C_q_prime_subproof.
  case (leqP p.-1 1%N) => [|H2p].
    by case: p p_prime => [|[|[|]]] //; rewrite !modn1.
  rewrite predn_exp mulKn; last by rewrite ltnW.
  rewrite -modn_summ -[q in X in _ = X]card_ord -sum1_card.
  apply: f_equal2 => //; apply: eq_bigr => i _.
  rewrite -modnXm -{1}[p]prednK ?prime_gt0 //.
  by rewrite -addn1 modnDl [X in (X ^ _)%N]modn_small // exp1n modn_small.
rewrite dprodE /=; last by apply: coprime_TIg.
  apply/eqP.
  rewrite eqEcard subsetT coprime_cardMg //.
  rewrite card_psiU card_Fp finField_unit_card Fcard.
  rewrite predn_exp mulKn; first by rewrite mulnC leqnn.
  by rewrite -ltnS prednK ?prime_gt0 // prime_gt1.
apply: subset_trans (centS (subsetT _)).
apply: (subset_trans (subsetT _)).
apply: cyclic_abelian.
by apply: field_unit_group_cyclic.
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

Hypothesis BG_appendix_C2a : 4 < q -> 1 < #|E|.
(* TODO *)

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

Lemma BG_appendix_C3_1 x : x \in H ->
  exists u, exists v, exists s1, 
  [/\ u \in U, v \in U, s1 \in P0 & x = u * s1 * v].
Proof.
case/Frobenius_context: HfrobHPU => HPUH _ _ _ _.
case/(mem_sdprod HPUH) => s' [u' [Hs' Hu' -> Hs'u']].
case: (eqVneq s' 1) => [Hs1|Hs_neq1].
  exists u'; exists 1; exists 1.
  by split => //; rewrite !mulg1 Hs1 mul1g.
have Hsigma_s' : sigma s' \is a GRing.unit.
  rewrite unitfE -[0](morph1 sigma) (inj_in_eq (injmP _ (isom_inj Hsigma))) //.
  by rewrite group1.
have := in_setT (FinRing.Unit _ Hsigma_s').
rewrite -(dprodW BG_appendix_C_remark_VIII).
case/mulsgP => _ s1 /morphimP [u Hu _ ->] Hs1 /(f_equal val) /= Hsvs1.
have Hinvs1 : isom_inv Hsigma (val s1) \in P0.
  rewrite -(morphim_invm (isom_inj Hsigma) HP0P).
  apply: mem_morphim; first by rewrite /= (isom_im Hsigma) in_setT.
  rewrite morphimEsub // HP0Fp.
  case/morphimP: Hs1 => /= k _ _ -> /=.
  by rewrite Fpis1; apply: memvZ; apply: mem1v.
have Hinvs1P : isom_inv Hsigma (val s1) \in P by apply: (subsetP HP0P).
exists (u^-1); exists (u * u'); exists (isom_inv Hsigma (val s1)).
rewrite groupV; split => [//||//|]; first by rewrite groupM.
rewrite mulgA; congr (_ * _)%g; rewrite -mulgA -conjgE.
apply: (injmP _ (isom_inj Hsigma)); first done.
  by apply: Pconj.
by rewrite Hsvs1 Hpsi // invmK // (isom_im Hsigma) in_setT.
Qed.

Lemma BG_appendix_C3_2 s1 s2 u :
  s1 \in P0 -> s2 \in P0 -> u \in U -> s1 * u * s2 \in U ->
  (s1 == 1) && (s2 == 1) || (u == 1) && (s1 * s2 == 1).
Proof.
case/Frobenius_context: HfrobHPU => /sdprodP [_ _ _ HPUI] _ _ _ _ Hs1 Hs2 Hu.
have Hs1P := subsetP HP0P _ Hs1.
have Hs2P := subsetP HP0P _ Hs2.
case: (boolP (s1 == 1)) => [/eqP ->|Hs1_neq1].
  by rewrite mul1g groupMl // -in_set1 -[[set 1]]HPUI inE Hs2P => ->.
case: (boolP (s2 == 1)) => [/eqP ->|Hs2_neq1].
  rewrite mulg1 groupMr // => Hs1U.
  move: Hs1_neq1.
  by rewrite -in_set1 -[[set 1]]HPUI inE Hs1U Hs1P.
move => Hs1us2.
suff /eqP Hu1 : u == 1.
  rewrite Hu1 eqxx /= -in_set1 -[[set 1]]HPUI inE groupM //=.
  move: Hu1 Hs1us2 ->.
  by rewrite mulg1.
rewrite -(inj_in_eq (injmP _ psi_injm_subproof)) ?group1 //.
rewrite morph1 -in_set1 //.
case: (dprodP BG_appendix_C_remark_VIII) => _ _ _ HUFp1.
rewrite -[[set 1]]HUFp1 {HUFp1} inE mem_morphim //=.
have : s1 ^ u * s2 == 1.
  rewrite -in_set1 -[[set 1]]HPUI inE.
  rewrite groupM ?PU_conj ?groupV //.
  move: Hs1us2.
  by rewrite [s1 * u]conjgC -mulgA groupMl.
rewrite -(inj_in_eq (injmP _ (isom_inj Hsigma)))
        ?group1 1?groupM ?PU_conj ?groupV //.
rewrite morphM ?PU_conj ?groupV // morph1 Hpsi ?groupV // addr_eq0.
have : sigma s1 != 0.
  by rewrite -[0](morph1 sigma) (inj_in_eq (injmP _ (isom_inj Hsigma))) ?group1.
have : sigma s2 != 0.
  by rewrite -[0](morph1 sigma) (inj_in_eq (injmP _ (isom_inj Hsigma))) ?group1.
have := mem_imset sigma Hs1.
have := mem_imset sigma Hs2.
rewrite HP0Fp !Fpis1.
move => /vlineP [k2 ->] /vlineP [k1 ->].
rewrite 2!(fmorph_eq0 [rmorphism of in_alg sfF]).
move => Hk20 Hk10.
rewrite -[- (k2 *: (1%:R:sfF))](rmorphN [rmorphism of in_alg sfF]).
rewrite (canF_eq (mulfK _)) ?(fmorph_eq0 [rmorphism of in_alg sfF]) //.
rewrite -(fmorphV [rmorphism of in_alg sfF]) -rmorphM.
move /eqP => Hpsiu.
rewrite morphimEdom.
apply/imsetP => /=.
have Hk2k1 : (- k2 / k1)%R \is a GRing.unit.
  by rewrite unitfE mulf_eq0 oppr_eq0 invr_eq0 negb_or Hk20 Hk10.
exists (FinRing.Unit _ Hk2k1); first by rewrite inE.
apply:val_inj.
by rewrite Hpsiu /=.
Qed.

Hypothesis BG_appendix_C3 : odd p -> E = [set (x^-1)%R | x in E].
(* TODO *)

Theorem BG_appendix_C : p <= q.
Proof.
have q_prime := BG_appendix_C_q_prime_subproof.
have [p2 | p_odd] := even_prime p_prime.
  by rewrite p2 prime_gt1.
have [q2 | q_odd] := even_prime q_prime.
  move: Hpq.
  by rewrite q2 dvdn2 -subn1 odd_sub ?p_odd ?prime_gt0.
apply: BG_appendix_C1; first by apply BG_appendix_C3.
case: (eqVneq q 3) => Hq3; first by apply: BG_appendix_C2b.
apply: BG_appendix_C2a.
by case: q q_odd q_prime Hq3 => [|[|[|[|[|]]]]].
Qed.

End AppendixC.
