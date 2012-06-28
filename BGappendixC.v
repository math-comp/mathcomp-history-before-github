Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat div prime seq.
Require Import fintype finfun ssralg finalg finset fingroup morphism bigop.
Require Import abelian frobenius zmodp finfield poly vector falgebra galois.
Require Import polydiv fieldext cyclic.

(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope group_scope.
Open Local Scope ring_scope.
Import GRing.Theory.
Import PrimeFieldExt.

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

Variable Q : {group gT}.
Hypothesis HQ : q.-abelem Q.

Variable W2 : {group gT}. 
Hypothesis HW2P : W2 \subset P.
Hypothesis HFpQ : W2 \subset 'N(Q).

Variable y : gT.
Hypothesis HyQ : y \in Q.
Hypothesis HFpUy : W2 \subset 'N(U :^ y).

CoInductive finFieldImage : Type :=
  FinFieldImage (F : finFieldType) (sigma : {morphism P >-> F})
                (rho : gT -> F) (_ : isom P [set: F] sigma)
                (_ : forall a b, a \in P -> b \in U -> 
                                 sigma (a ^ b) = rho b * sigma a).

Variable FSigmaRho : finFieldImage.

Let F : finFieldType :=
  let: FinFieldImage F _ _ _ _ := FSigmaRho in F.

Let sigma : {morphism P >-> F} :=
  let (_,sigma,_,_,_) as FST
  return {morphism P >-> ((let: FinFieldImage F _ _ _ _ := FST in F)
                          : finFieldType)}
  := FSigmaRho in sigma.

Let Hsigma : isom P [set: F] sigma.
Proof. by rewrite /sigma /F; case: FSigmaRho. Qed.

Let Fp := <[(1%R : F)]>.

Hypothesis HW2Fp : sigma @: W2 = Fp.

Let sfF : splittingFieldType _ := [splittingFieldType _ of F] .

Local Notation "`| x |" := (galNorm 1 {:sfF} x).

Let E := [set x | `| x | == 1 & `| 2%:R - x | == 1].

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

Let Fdim : \dim {:sfF} = q.
Proof.
have /expnI : 1 < finChar F by rewrite prime_gt1 // finChar_prime.
apply.
rewrite -finField_dimv_card [X in (X ^ _)%N]Fchar -Fcard.
by apply: eq_card => ?; rewrite memvf.
Qed.

Lemma E_nontriv : 1 \in E.
Proof. by rewrite !inE -addrA subrr addr0 galNorm1 eqxx. Qed.

Lemma two_minus_E x : (x \in E) = (2%:R - x \in E).
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
have galPoly_roots : all (root (galPoly - 1)) (enum (1%VS : {vspace sfF})).
  apply/allP => b; rewrite mem_enum.
  move/vlineP => {b} [k ->].
  rewrite rootE !hornerE horner_prod subr_eq0.
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
    rewrite -[X in X != _]Hgal mulf_eq0 galNorm_eq0 negb_or.  
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
  rewrite size_prod; last by move => i _; rewrite -size_poly_eq0 Hfactor.
  set S := (\sum_(i in Gal) _)%N.
  have -> : S = (\sum_(i in Gal) 2)%N by apply: eq_bigr => i _; apply: Hfactor.
  rewrite sum_nat_const -add1n mulnC !addnA addn0 addnK add1n.
  have /galois_dim <- := galoisFiniteField (sub1v {:sfF}).
  by rewrite dimv1 divn1 Fdim.
have size_galPoly1 : size (galPoly - 1) = q.+1.
  by rewrite size_addl // size_opp size_poly1 size_galPoly ltnS lt0n.
rewrite -size_galPoly1.
have galPoly1_neq0 : galPoly - 1 != 0.
  by rewrite -size_poly_eq0 size_galPoly1.
rewrite -[p]expn1 -(@dimv1 _ sfF) -Fchar -finField_dimv_card cardE.
by apply: max_poly_roots => //; apply: enum_uniq.
Qed.

(*
Lemma BG_appendix_C2b : q = 3 -> 1 < #|E|.
Proof.
move => Hq3.
rewrite (cardsD1 1) E_nontriv add1n ltnS card_gt0.
apply/set0Pn => /=.
pose f c : {poly F} := 'X * ('X - 2%:R%:P) * ('X - c%:A%:P) + ('X - 1).
have /= Hf0 c : ~~ root (f c) 0 by rewrite /root !hornerE oppr_eq0 oner_eq0.
have /= Hf2 c : ~~ root (f c) 2%:R.
  by rewrite /root !(hornerE, subrr) -(@natrB _ 2 1) // oner_neq0.
have /= Hf_root a b d : root (f a) d -> root (f b) d -> a = b.
  move => Hfa Hfb.
  have Hd_neq0 : d != 0 by apply: contra (Hf0 a) => /eqP <-.
  have Hd_neq2 : (d - 2%:R) != 0.
    by rewrite subr_eq0; apply: contra (Hf2 a) => /eqP <-.
  move: Hfb Hfa; rewrite /root => /eqP <-.
  rewrite !hornerE /= 2!(can_eq (addrK _)) -!mulrA.
  rewrite (can_eq (mulKf Hd_neq0)) (can_eq (mulKf Hd_neq2)).
  rewrite (can_eq (addKr _)) eqr_opp -!in_algE (inj_eq (fmorph_inj _)).
  by apply/eqP.
case: (boolP [forall c, exists d, root (f c) (d%:A)]).
  move/forallP => Hrootf.
  pose ch c := xchoose (existsP (Hrootf c)).
  suff [chinv chK chinvK] : bijective ch.
    move: (chinvK 0) (xchooseP (existsP (Hrootf (chinv 0)))) (Hf0 (chinv 0)).
    by rewrite /ch => ->; rewrite scale0r => ->.
  rewrite /ch.
  apply: injF_bij => a b Hab.
  apply: (Hf_root _ _ (xchoose (existsP (Hrootf a)))%:A).
    by apply: (xchooseP (existsP (Hrootf _))).
  by rewrite Hab; apply: (xchooseP (existsP (Hrootf _))).
rewrite negb_forall => /existsP /= [c].
rewrite negb_exists => /forallP /= Hc.
have size_fcr :
  size (('X : {poly F}) * ('X - (2%:R)%:P) * ('X - (c%:A)%:P)) = 4.
  rewrite -mulrA mulrC size_mulX ?mulf_eq0 ?polyXsubC_eq0 //.
  by rewrite size_mul ?polyXsubC_eq0 // !size_XsubC.
have size_fc : size (f c) = 4 by rewrite size_addl ?size_XsubC size_fcr.
have fc_monic : f c \is monic.
  rewrite /f monicE lead_coefDl ?size_XsubC ?size_fcr //.
  by rewrite -monicE !monicMl ?monicXsubC ?monicX.
have fc_over1 : f c \is a polyOver 1%AS.
  by rewrite !(rpredD, rpredM) ?rpredN ?polyOverX //
             ?polyOverC ?rpredZ ?rpredMn ?memv_line.
have fc_irr r : r \is a polyOver 1%AS -> size r != 1%N -> r %| f c -> r %= f c.
  (* Genrealize this lemma? *)
  move => Hr1 r_size Hrf.
  move/dvdp_size_eqp: (Hrf) <-.
  rewrite eqn_leq dvdp_leq ?monic_neq0 //=.
  rewrite leqNgt.
  have {r_size} r_size : (1 < size r).
    suff : size r != 0%N by case: (size r) r_size => //; case.
    rewrite size_poly_eq0.
    apply: contraTneq Hrf => ->.
    by rewrite dvd0p monic_neq0.
  apply/negP => /(conj r_size)/andP => {r_size} r_size.
  have {size_fc} size_fc : size (f c) <= 4 by rewrite size_fc.
  have [a] := cubic_polyOver_root fc_over1 Hr1 size_fc Hrf r_size.
  case/vlineP => k ->.
  by apply/negP.
suff [a Ha] : exists a, root (f c) a.
  have /eqP fc_min : minPoly 1 a == f c.
    rewrite -eqp_monic ?monic_minPoly //.
    by apply: fc_irr; rewrite ?minPolyOver ?size_minPoly ?minPoly_dvdp //.
  have Hgalois := galoisFiniteField (sub1v {:sfF}).
  have card_gal : #|'Gal({:sfF} / 1)| = 3.
    by rewrite -(galois_dim Hgalois) dimv1 divn1 Fdim.
  have fc_factor : f c = \prod_(x in 'Gal({:sfF} / 1)) ('X - (x a)%:P).
    rewrite -fc_min.
    have : size (minPoly 1 a) = (\dim_(1%AS : {vspace sfF}) {:sfF}).+1.
      by rewrite fc_min size_fc dimv1 divn1 Fdim Hq3.
    have /galois_factors [_] := Hgalois.
    case/(_ _ (memvf a)) => r [Hr /map_uniq Hr_uniq ->].
    rewrite big_map size_prod_XsubC big_uniq //=.
    case => size_r.
    move/card_uniqP: Hr_uniq; rewrite size_r (galois_dim Hgalois) => card_r.
    apply: eq_bigl.
    by apply/(subset_cardP card_r).
  exists a; rewrite !inE; apply/and3P; split.
  - apply: contraTneq Ha => ->.
    by rewrite -[1]scale1r; apply Hc.
  - rewrite -eqr_opp; apply/eqP.
    have -> : -1 = (f c).[0] by rewrite !hornerE.
    rewrite -mulN1r.
    have -> : -1 = (-1) ^+ #|'Gal({:sfF} / 1)| :> F.
      by rewrite card_gal -signr_odd expr1.
    rewrite -prodrN fc_factor horner_prod.
    by apply: eq_bigr => i _; rewrite !hornerE.
  - apply/eqP.
    transitivity (f c).[2%:R]; last first.
      by rewrite !hornerE /= subrr mulr0 mul0r add0r addrK.
    rewrite fc_factor horner_prod.
    by apply: eq_bigr => i _; rewrite rmorphB rmorphMn rmorph1 !hornerE.
apply/existsP.
rewrite -[[exists x, _]]negbK negb_exists.
apply/negP => /forallP => HnoRoot.
have : irreducible_poly (f c).
  (* Generalize this lemma? *)
  split => [|r r_size Hrf]; first by rewrite size_fc.
  move/dvdp_size_eqp: (Hrf) <-.
  rewrite eqn_leq dvdp_leq ?monic_neq0 //=.
  rewrite leqNgt.
  have {r_size} r_size : (1 < size r).
    suff : size r != 0%N by case: (size r) r_size => //; case.
    rewrite size_poly_eq0.
    apply: contraTneq Hrf => ->.
    by rewrite dvd0p monic_neq0.
  apply/negP => /(conj r_size)/andP => {r_size} r_size.
  have {size_fc} size_fc : size (f c) <= 4 by rewrite size_fc.
  have fc_over : f c \is a polyOver {:sfF}%AS.
    by apply/polyOverP => i; rewrite memvf.
  have r_over : r \is a polyOver {:sfF}%AS.
    by apply/polyOverP => i; rewrite memvf.
  have [a _] := cubic_polyOver_root fc_over r_over size_fc Hrf r_size.
  by apply/negP.
case/(@irredp_FAdjoin sfF) => L.
rewrite size_fc /= => Hdim [z Hz H1z].
pose Fz := <<1%AS; (z : baseField_vectType L)>>%AS.
have := (dim_baseVspace {:L}).
rewrite Hdim.
rewrite Fdim.
rewrite Hq3 => Hdim9.
have := size_minPoly (1%AS : {subfield baseField_vectType L}) z.
rewrite elementDegreeE.
rewrite dimv1 divn1.
rewrite 

*)

(* Lemma BG_appendix_C : p <= q. *)

End AppendixC.