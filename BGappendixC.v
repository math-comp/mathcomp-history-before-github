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

Variable y0 : gT.
Hypothesis Hy0Q : y0 \in Q.
Hypothesis HP0Uy0 : P0 \subset 'N(U :^ y0).

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

Let sfF : splittingFieldType _ := [splittingFieldType _ of primeFieldExtType F].

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

Let PU_conj : {in P & U, forall s' u, s' ^ u \in P}.
Proof.
move => s' u Hs' Hu /=.
rewrite memJ_norm //.
case: (Frobenius_context HfrobHPU) => /sdprodP [_ _ /subsetP HUP _] _ _ _ _.
by apply: HUP.
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
have := Hy0Q.
rewrite HQ1.
by move/set1P <-.
Qed.

Let q_neq0 : q != 0%N.
Proof. by rewrite -lt0n prime_gt0 // BG_appendix_C_q_prime_subproof. Qed.

Let Fcard : #|F| = (p ^ q)%N.
Proof. by rewrite -Pcard (isom_card Hsigma) cardsT. Qed.

Let Fchar : finChar F = p.
Proof.
rewrite /finChar Fcard.
move: q_neq0; rewrite -lt0n; move/prednK <-.
by rewrite pdiv_pfactor.
Qed.

Let Fdim : \dim {:sfF} = q.
Proof.
rewrite primeFieldExt_dimf.
have /expnI : 1 < finChar F by rewrite prime_gt1 // finChar_prime.
apply.
by rewrite -finField_card [X in (X ^ _)%N]Fchar -Fcard.
Qed.

Lemma BG_appendix_C_remark_I : coprime ((p ^ q).-1 %/ p.-1) p.-1.
Proof.
rewrite -coprime_modl.
suff -> : ((p ^ q).-1 %/ p.-1) = q %[mod p.-1].
  by rewrite coprime_modl prime_coprime // BG_appendix_C_q_prime_subproof.
case (leqP p.-1 1%N) => [|H2p].
  by case: p p_prime => [|[|[|]]] //; rewrite !modn1.
rewrite predn_exp mulKn; last by rewrite ltnW.
rewrite -modn_summ -[q in X in _ = X]card_ord -sum1_card.
apply: f_equal2 => //; apply: eq_bigr => i _.
rewrite -modnXm -{1}[p]prednK ?prime_gt0 //.
by rewrite -addn1 modnDl [X in (X ^ _)%N]modn_small // exp1n modn_small.
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

Local Notation "`| x |" := (galNorm 1 {:sfF} x).

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
- by rewrite card_psiU card_Fp BG_appendix_C_remark_I.
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

Hypothesis BG_appendix_C_remark_X : 'C_Q(P0) \x [~: Q, P0] = Q.
(* TODO *)

Lemma BG_appendix_C_remark_XI : {y | y \in [~: Q, P0] & P0 :^ y \subset 'N(U)}.
Proof.
suff Hy : exists y, (y \in [~: Q, P0]) && (P0 :^ y \subset 'N(U)).
  have /andP [Hy1 Hy2] := xchooseP Hy.
  by exists (xchoose Hy).
have : (y0^-1)%g \in Q by rewrite groupV.
case/(mem_dprod BG_appendix_C_remark_X) => x [y [Hx Hy Hy0 _]].
exists y; rewrite Hy /=.
move: Hx; rewrite inE; case/andP => _ /(subsetP (cent_sub _))/normP <-.
by rewrite -conjsgM -Hy0 sub_conjgV -normJ.
Qed.

Let y := let (y,_,_) := BG_appendix_C_remark_XI in y.

Let HyQP0 : y \in [~: Q, P0].
Proof. rewrite /y; by case: BG_appendix_C_remark_XI. Qed.

Let HyQ : y \in Q.
Proof.
have  [_ <- _ _]:= dprodP BG_appendix_C_remark_X.
by apply: (subsetP (mulG_subr _ _)).
Qed.

Let HP0yU : P0 :^ y \subset 'N(U).
Proof. rewrite /y; by case: BG_appendix_C_remark_XI. Qed.

Let E := [set x : sfF | `| x | == 1 & `| 2%:R - x | == 1].

Let E_nontriv : 1 \in E.
Proof. by rewrite !inE -addrA subrr addr0 galNorm1 eqxx. Qed.

Let two_minus_E x : (x \in E) = (2%:R - x \in E).
Proof. by rewrite !inE opprB addrA [2%:R + x]addrC addrK andbC. Qed.

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
rewrite -[[set 1]]HUFp1 {HUFp1} inE mem_morphim // morphimEdom //=.
apply/imsetP => /=.
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
rewrite 2!(fmorph_eq0 [rmorphism of in_alg sfF]) => Hk20 Hk10.
rewrite (canF_eq (mulfK _)) ?(fmorph_eq0 [rmorphism of in_alg sfF]) //.
rewrite -(rmorphN [rmorphism of in_alg sfF]).
rewrite -(fmorphV [rmorphism of in_alg sfF]) -rmorphM => /eqP Hpsiu.
have Hk2k1 : (- k2 / k1)%R \is a GRing.unit.
  by rewrite unitfE mulf_eq0 oppr_eq0 invr_eq0 negb_or Hk20 Hk10.
exists (FinRing.Unit _ Hk2k1); first by rewrite inE.
by apply:val_inj.
Qed.

Hypothesis BG_appendix_C3_3 : forall t1, t1 \in P1^# -> H :&: H :^ t1 = U.
(*TODO*)

Lemma BG_appendix_C3 : odd p -> E = [set (x^-1)%R | x in E].
Proof.
move => p_odd.
have HtP1 : t \in P1 by apply: mem_imset.
have U_abelian : abelian U.
  apply/centsP => u Hu v Hv.
  apply: (injmP _ psi_injm_subproof); rewrite ?groupM //.
  rewrite !morphM //.
  by apply (centsP (cyclic_abelian (field_unit_group_cyclic [set: {unit F}])));
    rewrite inE.
have HUconj r : r \in P1 -> U :^ r = U.
  by move => Hr; apply/normP; rewrite (subsetP HP0yU) //; apply: mem_imset.
have HutnU u n : u \in U -> u ^ (t ^+ n) \in U.
  move => Hu.
  rewrite -(HUconj (t ^+ n)) ?groupX //.
  by apply: mem_imset.
have HutNnU u n : u \in U -> u ^ (t ^- n) \in U.
  move => Hu.
  rewrite -(HUconj (t ^- n)) ?groupV ?groupX //.
  by apply: mem_imset.
have HtsQ i : s ^- i * t ^+ i \in Q.
  rewrite -conjXg !mulgA groupM // -mulgA memJ_norm ?groupV // groupX //.
  by apply: (subsetP HP0Q).
suff Hsuff a : a \in U ->
  val (psi a) \in E -> val (psi ((a^-1) ^ (t ^+ 3))) \in E.
- suff : [set (x^-1)%R | x in E] \subset E.
    rewrite (eq_imset (g:=(GRing.inv))) // => HE.
    apply/eqP.
    by rewrite eqEsubset HE (can_imset_pre _ (@invrK _)) -sub_imset_pre HE.
  apply/subsetP => _ /imsetP [x x_in_E ->].
  move: x_in_E (x_in_E); rewrite {1}inE => /andP [Hx H2x].
  have : x \in (val : {unit F} -> F) @: (psi @* U).
    by rewrite BG_appendix_C_remark_VII inE.
  rewrite morphimEdom -imset_comp.
  case/imsetP => a Ha /= -> HaE.
  rewrite -val_unitV -morphV // -[a^-1]conjg1.
  have /eqP <- : (t ^+ (3 * p ^ q)) == 1.
    rewrite -order_dvdn dvdn_mull // orderJ -Fcard -cardsT -(isom_card Hsigma).
    by rewrite order_dvdG.
  have -> : a^-1 = if odd (p ^ q) then a^-1 else a.
    by rewrite odd_exp p_odd orbT.
  elim: (p ^ q)%N => [|n /=]; first by rewrite muln0 expg0 conjg1.
  rewrite mulnSr expgD conjgM.
  suff : (if odd n then a^-1 else a) ^ t ^+ (3 * n) \in U.
    by case: ifP => _ HinU /(Hsuff _ HinU) /=; rewrite -conjVg ?invgK.
  by apply: HutnU; rewrite fun_if if_arg groupV if_same.
rewrite 2!inE => Ha /andP [_ Hb].
have Hainvt3 : a^-1 ^ t ^+ 3 \in U by apply: HutnU; rewrite groupV.
apply/andP; split.
  have : val (psi (a^-1 ^ t ^+ 3)) \in (val : {unit F} -> F) @: (psi @* U).
    by apply: mem_imset; apply: mem_morphim.
  by rewrite BG_appendix_C_remark_VII inE.
pose goal v1 := s ^+ 2 = s ^ v1 * s ^ (a^-1) ^ t ^+ 3.
suff [v1 Hv1U] : exists2 v1, v1 \in U & goal v1.
  move/(f_equal sigma).
  rewrite morphX // morphM ?Pconj // sigma_s -psiE // -psiE // zmodXgE zmodMgE.
  move/(canLR (addrK _)) ->.
  have : val (psi v1) \in (val : {unit F} -> F) @: (psi @* U).
    by apply: mem_imset; apply: mem_morphim.
  by rewrite BG_appendix_C_remark_VII inE.
have : 2%:R - val (psi a) \in (val : {unit F} -> F) @: (psi @* U).
  by rewrite BG_appendix_C_remark_VII inE.
rewrite morphimEdom -imset_comp.
case/imsetP => {Hainvt3 Hb} b Hb /eqP.
rewrite (canF_eq (addrNK _)) addrC => Hab.
(* In the book k is aribtrary in Fp; however only k := 3 is used *)
pose k := 3.
case/Frobenius_context: HfrobHPU => /sdprodP [_ HPU _ HPUI] _ _ _ _.
have C5inH m n r u : u \in U -> s ^+ m * u ^ t ^+ r * s ^- n \in H.
  move => Hu.
  apply: groupM; first apply groupM; rewrite ?groupV ?groupX // -HPU.
  - by apply: (subsetP (mulG_subl U P)).
  - by apply: (subsetP (mulG_subr P U)); apply: HutnU.
  - by apply: (subsetP (mulG_subl U P)).
case: (@BG_appendix_C3_1 (s ^+ k.-2 * a^-1 ^ t ^+ k * s ^- k.-1))
    => [|u1 [v1 [s1 [Hu1 Hv1 Hs1 Husv1]]]].
  by apply: C5inH; rewrite groupV.
case: (@BG_appendix_C3_1 (s ^+ k * (a * b^-1) ^ t ^+ k.-1 * s ^- k.-2))
    => [|u2 [v2 [s2 [Hu2 Hv2 Hs2 Husv2]]]].
  by apply: C5inH; rewrite groupM ?groupV //.
case: (@BG_appendix_C3_1 (s ^+ k.-1 * b ^ t ^+ k.-2 * s ^- k))
  => [|u3 [v3 [s3 [Hu3 Hv3 Hs3 Husv3]]] {C5inH}].
  by apply: C5inH.
exists v1; first done.
have C6 m n r u ui vi si : s ^+ m * u ^ t ^+ r * s ^- n = ui * si * vi ->
  s ^+ m != s ^+ n -> (s ^+ m != 1) || (s ^- n != 1) ->
  u \in U -> ui \in U -> vi \in U -> si != 1.
- case: (eqVneq si 1) => [->|//].
  rewrite mulg1 => Huv Hmn HmVn Hu Hui Hvi.
  have Hsm : s ^+ m \in P0 by apply: groupX.
  have Hsn : s ^- n \in P0 by rewrite groupV; apply: groupX.
  have Hut : u ^ t ^+ r \in U by apply: HutnU.
  have := groupM Hui Hvi; rewrite -Huv.
  case/(BG_appendix_C3_2 Hsm Hsn Hut)/orP.
    by move: HmVn; rewrite -negb_and; case: (_ && _).
  by rewrite -eq_mulgV1 andbC; case: (s ^+ _ == _) Hmn.
have ss_neq_1 : s ^+ 2 != 1.
  rewrite -order_dvdn.
  apply/prime_nt_dvdP => //; first by rewrite order_eq1.
  apply/eqP.
  case: (eqVneq #[s] 2) (order_dvdG s_P) => [->|//].
  by rewrite (isom_card Hsigma) cardsT Fcard dvdn2 odd_exp p_odd orbT.
have s1neq1 : s1 != 1.
  apply: (C6 _ _ _ _ _ _ _ Husv1); rewrite ?groupV //.
    by rewrite eq_mulVg1 !(expg1, expgS) mulKg.
  by rewrite expg1 s_neq_1.
(*
have s2neq1 : s2 != 1.
  apply: (C6 _ _ _ _ _ _ _ Husv2); rewrite ?groupM ?groupV //.
    by rewrite eq_mulgV1 !(expg1, expgS) mulgA mulgK.
  by rewrite eq_invg1 expg1 s_neq_1 orbT.
*)
have s3neq1 : s3 != 1.
  apply: (C6 _ _ _ _ _ _ _ Husv3) => //.
    by rewrite eq_mulVg1 !(expg1, expgS) !invMg -!mulgA !mulKg.
  by rewrite ss_neq_1.
clear C6.
pose w1 := v2 ^ t^-1 * u3.
pose w2 := v3 * u1 ^ t ^- 2.
pose w3 := v1 * u2 ^ t.
wlog suff C7_gen : a b u1 s1 v1 u2 s2 v2 u3 s3 v3 
  Husv1 Husv2 Husv3 Hab Ha Hb Hu1 Hs1 Hv1 Hu2 Hs2 Hv2 Hu3 Hs3 Hv3
  @w1 @w2 @w3 {s1neq1 (*s2neq1*) s3neq1 goal} /
  t^-1 * s2 * t^-1 = ((w1 * s3 * w2) * (t ^+ 2 * s1 * w3))^-1; last first.
- apply/eqP; rewrite invMg -(canF_eq (mulgK _)) eq_sym eq_invg_mul; apply/eqP.
  move: Hab; rewrite eq_sym -subr_eq0 addrC.
  rewrite -sigma_s /= {1}(psiE Ha) (psiE Hb).
  rewrite -zmodXgE -morphX // -zmodVgE -morphV ?groupX //.
  rewrite -!zmodMgE -!morphM ?(morph_injm_eq1 (isom_inj Hsigma))
          ?(groupV, Pconj, groupX, groupM) //.
  pose l := (k - 2)%N.
  rewrite -(conjg_eq1 _ (t ^+ l)).
  rewrite [X in X == _](_ : _ = 
    ((t ^- l * s ^+ l) * (s ^- k * t ^+ k)) * a^-1 ^ t ^+ k *
    ((t ^- k * s ^+ k) * (s ^- k.-1 * t ^+ k.-1)) * (a * b^-1) ^ t ^+ k.-1 * 
    ((t ^- k.-1 * s ^+ k.-1) * (s ^- l * t ^+ l)) * b ^ t ^+ l *
    s ^- k * s ^+ k); last by rewrite /t !conjgE !invMg !mulgA !mulgK !mulgKV.
  have ts_commute m n : commute (t ^- m * s ^+ m) (s ^- n * t ^+ n).
    apply: (centsP (abelem_abelian HQ)) => //.
    by rewrite -groupV invMg invgK.
  rewrite !ts_commute {ts_commute} -(conjg_eq1 _ (s ^- k)).
  set C5a := s ^+ k.-2 * a^-1 ^ t ^+ k * s ^- k.-1.
  set C5b := s ^+ k * (a * b^-1) ^ t ^+ k.-1 * s ^- k.-2.
  set C5c := s ^+ k.-1 * b ^ t ^+ k.-2 * s ^- k.
  rewrite [X in X == _](_ : _ = t ^+ 2 * C5a * t^-1 * C5b * t^-1 * C5c);
      last first.
    rewrite /C5a /C5b /C5c expgS expg1 /t !conjgE.
    by rewrite !invMg -!mulgA !mulKg !mulKVg !invgK.
  rewrite [C5a]Husv1 [C5b]Husv2 [C5c]Husv3 -(conjg_eq1 _ (u1 ^ t ^- 2)).
  move/eqP <-; rewrite /w1 /w2 /w3 -!conjXg !conjgE !(invgK, invMg) !mulgA.
  by rewrite !(mulgK, mulgKV).
have C7 : t^-1 * s2 * t^-1 = (w1 * s3 * w2 * (t ^+ 2 * s1 * w3))^-1.
  by apply: (C7_gen a b).
have moduloP u ui si vi m n r : s ^+ m * u ^ t ^+ r * s ^- n = ui * si * vi ->
  u \in U -> ui \in U -> si \in P0 -> vi \in U -> ui * vi = u ^ t ^+ r.
- rewrite [_ * si]conjgCV -2!mulgA [_ * s ^- n]conjgCV {1}mulgA.
  move/(canRL (mulgK _)); rewrite -mulgA; move/(canLR (mulKg _)) => Husvi.
  move => Hu Hui Hsi Hvi.
  apply/eqP; rewrite eq_mulgV1; apply/eqP/set1P.
  rewrite -[[set 1]]HPUI inE -{1}Husvi.
  rewrite !(HutnU, PU_conj, groupV, groupM) ?groupX //.
  by apply: (subsetP HP0P).
have : t^-1 * s2 * t^-1 = (w1 ^+ p * s3 * w2 ^+ p * (t ^+ 2 * s1 * w3 ^+ p))^-1.
- pose ap := a ^+ p; pose bp := b ^+ p.
  have Hapbp : 2%:R == val (psi ap) + (val \o psi_morph) bp.
    rewrite /= !morphX // !val_unitX.
    rewrite -Fchar -!(Frobenius_autE (finCharP F)) -rmorphD.
    rewrite -(rmorph_nat [rmorphism of (Frobenius_aut (finCharP F))]) inj_eq //.
    by apply: fmorph_inj.
  suff Husvp u ui si vi m n r : s ^+ m * u ^ t ^+ r * s ^- n = ui * si * vi ->
    u \in U -> ui \in U -> si \in P0 -> vi \in U ->
    s ^+ m * (u ^+ p) ^ t ^+ r * s ^- n = ui ^+ p * si * vi ^+ p.
  - have -> : w1 ^+ p = (v2 ^+ p) ^ t^-1 * u3 ^+ p.
      rewrite conjXg expgMn //; apply: (centsP U_abelian) => //.
      by rewrite -[t]expg1 HutNnU.
    have -> : w2 ^+ p = v3 ^+ p * (u1 ^+ p) ^ t ^- 2.
      rewrite conjXg expgMn //; apply: (centsP U_abelian) => //.
      by rewrite HutNnU.
    have -> : w3 ^+ p = v1 ^+ p * (u2 ^+ p) ^ t.
      rewrite conjXg expgMn //; apply: (centsP U_abelian) => //.
      by rewrite -[t]expg1 HutnU.
    apply: (C7_gen ap bp) => //; try apply: groupX => //.
    - by rewrite -[ap^-1]expgVn; apply: Husvp => //; rewrite groupV.
    - rewrite -[bp^-1]expgVn -expgMn; last first.
        by apply: (centsP U_abelian); rewrite // groupV.
      by apply: Husvp => //; rewrite groupM // groupV.
    - by apply: Husvp => //.
  move => Husvi Hu Hui Hsi Hvi.
  have Huivi := moduloP _ _ _ _ _ _ _ Husvi Hu Hui Hsi Hvi.
  move: (Husvi).
  rewrite [_ * si]conjgCV -2!mulgA [_ * s ^- n]conjgCV {1}mulgA -Huivi.
  move/(can_inj (mulgK _))/eqP; rewrite eq_sym.
  rewrite (canF_eq (conjgKV _)) conjMg -conjgM invMg mulgKV conjVg !conjXg.
  move/eqP/(f_equal (fun x => Frobenius_aut (finCharP F) (sigma x)))/eqP.
  rewrite morphM ?morphV ?morphX -?psiE ?groupV ?groupX ?PU_conj ?groupV //.
  rewrite rmorphB !zmodXgE -![val _ *+ _]mulr_natl !rmorphM !rmorph_nat /=.
  rewrite !Frobenius_autE.
  have : sigma si \in (1%VS : {vspace sfF}).
    by rewrite -Fpis1 -HP0Fp; apply: mem_imset.
  rewrite [_ \in _]fermat's_little_theorem dimv1.
  rewrite expn1 card_Fp ?finChar_prime // => /eqP ->.
  rewrite Fchar -!val_unitX -![psi _ ^+ p]morphX ?groupV //.
  rewrite !mulr_natl !psiE ?groupX ?groupV //.
  rewrite -!zmodXgE -![sigma _ ^+ _]morphX ?PU_conj ?groupX ?groupV // -zmodVgE.
  rewrite -zmodMgE -morphV -?morphM ?groupV ?groupX ?PU_conj ?groupX ?groupV //.
  rewrite -!conjXg -conjVg expgVn.
  rewrite (inj_in_eq (injmP _ (isom_inj Hsigma))); last first.
  - by rewrite groupM ?groupV ?groupX ?PU_conj ?groupX ?groupV ?groupX.
  - by apply: (subsetP HP0P).
  move/eqP ->.
  rewrite -!mulgA mulKVg; congr (_ * _); rewrite !mulgA mulgKV; congr (_ * _).
  rewrite [(_ ^- _)^-1]invgK -expgMn ?Huivi; last by apply: (centsP U_abelian).
  by rewrite -!conjXg -!mulgA.
rewrite C7 {C7_gen}.
move/invg_inj.
rewrite [X in X = _](_ : _ = w1 * s3 * w2 * t ^+ 2 * (s1 * w3));
  last by rewrite !mulgA.
rewrite [X in _ = X](_ : _ = w1 ^+ p * s3 * w2 ^+ p * t ^+ 2 * (s1 * w3 ^+ p));
  last by rewrite !mulgA.
move/(canLR (mulKg _)); rewrite mulgA; move/(canRL (mulgK _)).
rewrite [X in X = _](_ : _ = 
  ((w1 ^+ p * s3 * w2 ^+ p)^-1 * (w1 * s3 * w2)) ^ t ^+ 2); last first.
- by rewrite conjgE !(invMg, mulgA).
move => Hw.
have Hw1 : w1 \in U by rewrite groupM // -[t]expg1 HutNnU.
have Hw2 : w2 \in U by rewrite groupM // HutNnU.
have Hw3 : w3 \in U by by rewrite groupM // -[t]expg1 HutnU.
have : (s1 == 1) && (s1^-1 == 1) || (w3 ^+ p * w3^-1 == 1) && (s1 * s1^-1 == 1).
  apply: BG_appendix_C3_2; rewrite ?groupV //.
  - by rewrite groupM ?groupV ?groupX. 
  have Ht2 : t ^+ 2 \in P1^#.
    by rewrite 2!inE groupX // andbT -conjXg conjg_eq1.
  rewrite [X in X \in _](_ : _ =  s1 * w3 ^+ p * (s1 * w3)^-1);
    last by rewrite !invMg !mulgA.
  rewrite -(BG_appendix_C3_3 Ht2) inE -{2}Hw {Hw}.
  have /subsetP HUH : U \subset H by rewrite -HPU; apply: mulG_subr.
  move: w1 w2 w3 {C7 Hw1 Hw2 Hw3} (HUH _ Hw1) (HUH _ Hw2) (HUH _ Hw3).
  move => w1 w2 w3 Hw1 Hw2 Hw3.
  by apply/andP; split; last apply: mem_imset;
     rewrite !(groupV, groupM, groupX) // -HPU;
     apply: (subsetP (mulG_subl U P)); apply (subsetP HP0P).
rewrite eq_invg1 andbb (negbTE s1neq1) /=.
rewrite -[p]prednK ?prime_gt0 // expgSr mulgK.
have Hwp1 wi : wi \in U -> wi ^+ p.-1 == 1 -> wi = 1.
  move => Hwi Hwip1.
  apply/eqP; rewrite -[_ == 1]order_eq1 -dvdn1.
  have := BG_appendix_C_remark_I; rewrite /coprime => /eqP <-.
  by rewrite dvdn_gcd -Ucard order_dvdG // order_dvdn Hwip1.
case/andP => /(Hwp1 _ Hw3) w3_eq1 _.
move/eqP: Hw.
rewrite w3_eq1 expg1n mulg1 mulgV conjg_eq1 -eq_mulVg1.
rewrite -(canF_eq (mulKVg _)) invMg !mulgA (canF_eq (mulgK _)) => /eqP Hw.
have : (s3^-1 == 1) && (s3 == 1) || (w1^-1 * w1 ^+ p == 1) && (s3^-1 * s3 == 1).
  apply: BG_appendix_C3_2; rewrite ?groupV //.
  - by rewrite groupM ?groupV ?groupX.
  rewrite !mulgA Hw.
  by rewrite groupM ?groupV ?groupX.
rewrite eq_invg1 andbb (negbTE s3neq1) /=.
rewrite -[p]prednK ?prime_gt0 // expgS mulKg.
case/andP => /(Hwp1 _ Hw1) w1_eq1 _.
move/eqP: Hw.
rewrite !w1_eq1 invg1 expg1n !mulg1 mulVg eq_sym -eq_mulgV1 eq_mulVg1.
rewrite -[p]prednK ?prime_gt0 // expgS mulKg.
move/(Hwp1 _ Hw2) => w2_eq1.
move: C7.
rewrite {} w1_eq1 {} w2_eq1  {} w3_eq1 {w1 w2 w3 Hw1 Hw2 Hw3 Hwp1}.
rewrite !(mulg1, mul1g) => C7.
have P0_abelian : abelian P0.
  apply: cyclic_abelian.
  rewrite -(injm_cyclic (isom_inj Hsigma)) // morphimEsub // HP0Fp.
  by apply: cycle_cyclic.
have P0_cyclic : <[s]> = P0.
 apply: (injm_morphim_inj (isom_inj Hsigma)) => //.
   by rewrite cycle_subG.
  by rewrite morphim_cycle // morphimEsub // HP0Fp sigma_s.
have /eqP : s3 * s1 * s2 = 1.
  have := C7.
  case: (eqVneq (P0 :&: Q) 1) => [HP0QI|HP0QNI]; last first.
    have /subsetP HP0subQ : P0 \subset Q.
      apply: prime_meetG => //.
      rewrite -P0_cyclic -orderE.
      suff -> : #[s] = p by done.
      apply: nt_prime_order => //.
      apply: (injmP _ (isom_inj Hsigma)); rewrite ?group1 ?groupX //.
      rewrite morphX // morph1 zmodXgE -Fchar.
      apply: mulrn_char.
      apply: finCharP.
    have -> : t = s.
      apply/conjg_fixP/commgP.
      move/abelem_abelian/centsP: HQ; apply => //.
      by apply: HP0subQ.
    move/eqP; rewrite eq_sym eq_invg_mul.
    have -> : commute (s ^+ 2) s1.
      by apply: (centsP P0_abelian) => //; rewrite groupX.
    rewrite -[_ * s^-1]mulgA.
    have -> : commute s2 s^-1.
      by apply: (centsP P0_abelian) => //; rewrite groupV.
    rewrite expgS expg1 !mulgA !mulgK.
    by move/eqP.
  pose st := (s ^- 1 * t ^+ 1).
  have -> : t^-1 = st ^-1 * s^-1.
    by rewrite /st -invMg !expg1 mulKVg.
  rewrite -[t ^+ 2](mulKVg (s ^+ 2)).
  set st2 := (s ^-2 * t ^+ 2).
  rewrite 3!invMg -!mulgA.
  move/(canRL (mulKVg _)).
  rewrite [st^-1 * _]conjgC 3!mulgA [st * _]conjgC -[X in _ = X]mulgA.
  move/(canRL (mulgK _)).
  rewrite -[X in _ = X]mulgA.
  move/(canLR (mulKVg _)).
  rewrite [X in _ = X * _]mulgA [_ * (s ^- 2 * _)]conjgC -[X in _ = X]mulgA.
  rewrite -invMg.
  move/(canLR (mulKVg _)).
  have -> : commute s^-1 s2.
    by apply: (centsP P0_abelian); rewrite ?groupV.
  rewrite -[s2 * _ * _]mulgA [s1 * _]mulgA -invMg.
  have -> : commute (s1 * s2) (s * s)^-1.
    by apply: (centsP P0_abelian); rewrite !(groupV, groupM).
  rewrite mulgA expgS expg1 mulgK mulgA => Hs123.
  apply/set1P.
  rewrite -[[set 1]]HP0QI inE {2}Hs123.
  apply/andP; split; first by rewrite !groupM.
  rewrite groupM //; last first.
    by rewrite groupV memJ_norm groupV ?HtsQ // (subsetP HP0Q).
  rewrite memJ_norm; last by rewrite (subsetP HP0Q) // groupV !groupM.
  rewrite groupM //; last by rewrite groupV HtsQ.
  by rewrite memJ_norm ?HtsQ // groupV (subsetP HP0Q).
rewrite -eq_invg_mul eq_sym => /eqP s2E.
move/eqP: C7.
rewrite {}s2E {u2 v2 s2 Hu2 Hv2 Hs2 Husv2}.
rewrite [X in _ == X]invMg -(canF_eq (mulKg _)) eq_mulgV1 invgK.
rewrite -conjXg -{1}[s1](mulKg (s ^+ 2)) -conjVg.
rewrite -{1}(_ : (s^-2 * s) ^ s1 = s^-1); last first.
  rewrite invMg mulgKV.
  by apply/conjg_fixP/commgP; apply: (centsP P0_abelian); rewrite ?groupV.
rewrite -{1}[s3](mulgKV s) -{2}[s^-1](_ : s^-1 ^ s3^-1 = _); last first.
  by apply/conjg_fixP/commgP; apply: (centsP P0_abelian); rewrite ?groupV.
rewrite [X in X == _](_ : _ = 
  y^-1 * y ^ s ^- 2 * y^-1 ^ (s1^-1 * s ^- 2) * y ^ (s1^-1 * s^-1) *
  y^-1 ^ (s3 * s^-1) * y ^ s3); last by rewrite !conjgE !invMg !invgK !mulgA.
have := (mulG_subr 'C_Q(P0) [~: Q, P0]).
have  [_ -> _ _] := dprodP BG_appendix_C_remark_X.
move => HQP0Q.
have QP0_abelian : abelian [~: Q, P0].
  by apply: (abelianS HQP0Q); apply: (abelem_abelian HQ).
have /subsetP QP0_norm := commg_normr P0 Q.
pose x := y^-1 ^ s3 * y ^ s^-1 * y^-1 ^ (s1^-1 * s^-1) * y.
rewrite [X in X == _](_ : _ = x ^ s^-1 * x^-1); last first.
  rewrite 4!invMg -!conjVg invgK 3!conjMg -3!conjgM mulgA.
  set ysN2 := y ^ (s^-1 * s^-1).
  set yNs1N1sN2 := y^-1 ^ (s1^-1 * s^-1 * s^-1).
  set ys1N1sN1 := y ^ (s1^-1 * s^-1).
  set yNs3sN1 :=  y^-1 ^ (s3 * s^-1).
  set ys3 := y ^ s3.
  rewrite mulgA.
  have -> : commute (yNs3sN1 * ysN2 * yNs1N1sN2 * y ^ s^-1) y^-1.
    by apply: (centsP QP0_abelian);
      rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  rewrite [ys1N1sN1 * _]mulgA.
  have -> : commute ys1N1sN1 (y^-1 ^ s^-1).
    by apply: (centsP QP0_abelian);
      rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  rewrite 3!mulgA conjVg mulgK -[yNs3sN1 * _ * yNs1N1sN2]mulgA.
  rewrite -[X in _ = X * _]mulgA -[yNs3sN1 * _ * ys1N1sN1]mulgA.
  have -> : commute yNs3sN1  (ysN2 * yNs1N1sN2 * ys1N1sN1).
    by apply: (centsP QP0_abelian);
      rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  by rewrite 3!mulgA.
rewrite -eq_mulgV1 => /eqP Hx.
have {Hx} : x == 1.
  apply/eqP/set1P.
  have HxQP0 : x \in [~: Q, P0].
    by rewrite !(memJ_norm, QP0_norm, groupV, groupM) //.
  have [_ _ _ HCQP0I] := dprodP BG_appendix_C_remark_X.
  rewrite -[[set 1]]HCQP0I 2!inE (subsetP HQP0Q) HxQP0 //= andbT.
  rewrite -P0_cyclic -cycleV cent_cycle.
  by apply/cent1P/commgP/conjg_fixP.
pose t1 := s1 ^ y.
pose t3 := s3 ^ y.
have {x} -> : x = s3^-1 * (t3 * t) * (s1 * (t * t1)^-1).
  by rewrite /x conjVg !conjgE !invMg !mulgA !invgK !mulgK !mulgKV.
rewrite -eq_invg_mul invMg invgK => /eqP Hs1s3.
case: (eqVneq (t * t1)^-1 1) => [|Ht1t]; last first.
  suff Utriv u : u \in U -> u = 1.
    by rewrite /goal (Utriv v1) // (Utriv a) // invg1 conj1g conjg1 expgS expg1.
  have Ht1tP1 : (t * t1)^-1 \in P1^#.
    by rewrite 2!inE Ht1t groupV groupM //; apply: mem_imset.
  move => Hu.
  suff : (u ^ s1) ^ (t * t1)^-1 \in U.
    rewrite -mem_conjg HUconj; last by apply: groupM => //; apply: mem_imset.
    rewrite conjgE mulgA => Hus1U.
    have : (s1^-1 == 1) && (s1 == 1) || (u == 1) && (s1^-1 * s1 == 1).
      by apply: BG_appendix_C3_2; rewrite ?groupV.
    rewrite (negbTE s1neq1) andbF /=.
    by case/andP => /eqP.
  have Hs1H : s1 \in H.
    by rewrite -HPU (subsetP (mulG_subl _ _)) // (subsetP HP0P).
  have Hs3H : s3 \in H.
    by rewrite -HPU (subsetP (mulG_subl _ _)) // (subsetP HP0P).
  rewrite -(BG_appendix_C3_3 Ht1tP1) inE; apply/andP; split; last first.
    apply: mem_imset.
    by rewrite !groupM ?groupV // -HPU (subsetP (mulG_subr _ _)).
  rewrite -conjgM -Hs1s3 conjgM.
  apply: groupM; first by rewrite groupV; apply Hs3H.
  apply: groupM; last by apply Hs3H.
  rewrite -HPU (subsetP (mulG_subr _ _)) // -mem_conjg HUconj //.
  by apply: groupM => //; apply: mem_imset.
move/eqP.
rewrite {Hs1s3 t3 u3 v3 s3 Hu3 Hv3 Hs3 Husv3 s3neq1} -conjMg eq_invg1 conjg_eq1.
rewrite -eq_invg_mul => /eqP Hs1s.
have := moduloP _ _ _ _ _ _ _ Husv1 _ Hu1 Hs1 Hv1.
rewrite groupV; move/(_ Ha) => Hu1v1.
move/(canRL (mulgKV _))/(canLR (mulKg _)) : Husv1.
rewrite -{}Hs1s expg1 !invMg invgK /goal => <-.
rewrite [s * _ ^ _]conjgC.
rewrite mulgA; congr (_ * _); rewrite -!mulgA; congr (_ * (_ * _)).
by rewrite -Hu1v1 mulKg.
Qed.

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
