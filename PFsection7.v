(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator nilpotent.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import frobenius inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection4 PFsection5 PFsection6.

(******************************************************************************)
(* This file covers Peterfalvi, Section 7:                                    *)
(* Non-existence of a Certain Type of Group of Odd Order                      *)
(* Defined here:                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Seven.

Variable (gT : finGroupType) (G : {group gT}).

(* PF 7.1 - 7.3 *)
Section PF71_73.

Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha).

Local Notation Atau := (Dade_support ddA).

Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.


(**********************************)
(* 7.1 *)

Fact rho_subproof (chi : 'CF(G)) :
  is_class_fun <<L>> [ffun a => 
    if a \in A then #|H a|%:R ^-1 * (\sum_(x \in H a) chi (x * a)%g) else 0].
Proof.
rewrite genGid.
apply: intro_class_fun => [x y xL yL | x notLx]; last first.
  case xA: (x \in A) => //.
  by move: (subsetP sAL x xA); rewrite (negPf notLx).
have ->: x ^ y \in A = (x \in A).
  by rewrite memJ_norm // (subsetP nAL).
case xA: (x \in A) => //.
rewrite (DadeJ ddA) // cardJg.
congr (_ * _); rewrite big_imset /=; last first.
  by move => z y0 _ _ /=; exact: conjg_inj.
apply: eq_bigr => u uH.
rewrite !conjgE !mulgA !mulgK.
by rewrite -!mulgA [(u * _)%g]mulgA -conjgE cfunJ // (subsetP sLG).
Qed.

Definition rho_fun alpha := Cfun 1 (rho_subproof alpha).  

Lemma rho_is_linear : linear rho_fun.
Proof.
move=> mu alpha beta; apply/cfunP=> a; rewrite !cfunElock.
case: (_ \in _); last by rewrite mulr0 addr0.
rewrite -mulrCA -mulr_addr; congr (_ * _).
by rewrite -mulr_sumr -big_split; apply: eq_bigr => i _; rewrite !cfunE.
Qed.

Canonical rho_linear := Linear rho_is_linear.
Canonical rho_additive := Additive rho_is_linear.

Local Notation "alpha ^\rho" := (rho_fun alpha)
  (at level 2, format "alpha ^\rho").

Lemma support_rho chi : support chi^\rho \subset A.
Proof.
apply/subsetP=> x; rewrite !inE /rho_fun cfunElock;
by case: (_ \in _); rewrite ?(eqxx 0).
Qed.

Lemma rho_cfunS chi : chi^\rho \in 'CF(L, A).
Proof. by rewrite cfun_onE support_rho. Qed.

Lemma rho_1 : 1^\rho = '1_A.
Proof.
apply/cfunP => x; rewrite cfuniE; last by rewrite /normal sAL nAL.
rewrite cfunElock; case xA: (_ \in _); last by [].
rewrite -{2}(mulVf (neq0GC (H x))); congr (_ * _).
rewrite -sum1_card natr_sum.
apply: eq_bigr => u uH; rewrite cfun1E in_group.
  by move/subsetP: sAL => /(_ x xA); move/(subsetP sLG) ->.
case: ddA => _ _ _; move/(_ x xA)/sdprod_context => []/normal_sub/subsetIP[].
by move/subsetP/(_ u uH).
Qed.

Lemma rho_Dade_reciprocity chi alpha :
  alpha \in 'CF(L, A) -> '[alpha^\tau, chi] = '[alpha, chi^\rho].
Proof.
move=> Aalpha; apply: general_Dade_reciprocity => //= a Aa.
by rewrite cfunElock Aa.
Qed.

Lemma norm_chi_rho chi :
  '[chi^\rho] = #|L|%:R^-1 * (\sum_(a \in A) `|chi^\rho a| ^+ 2).
Proof. by apply: cfnormE; exact: rho_cfunS. Qed.

(* 7.2(a) *)
Lemma pf72a alpha : alpha \in 'CF(L, A) -> (alpha^\tau)^\rho = alpha.
Proof.
move => alphaC.
apply/cfunP => a; rewrite cfunElock.
case aA: (_ \in _); last by symmetry; apply: (cfun_on0 alphaC); rewrite aA.
rewrite -[alpha _]mul1r -{2}(mulVf (neq0GC (H a))) -mulrA.
congr (_ * _); rewrite -sum1_card natr_sum -mulr_suml mul1r.
apply: eq_bigr => u uHa.
rewrite (DadeE _ aA) //; apply: (subsetP (sub_class_support _ _)).
by apply: mem_mulg; first by []; exact: set11.
Qed.

(* 7.2(b) *)
Lemma pf72b chi : '[chi^\rho]_L <= '[chi]_G ?= iff (chi == (chi^\rho)^\tau).
Proof.
set w := (chi^\rho)^\tau.
have chi_rhoC := rho_cfunS chi.
have ortho: '[w, chi - w]_G = 0.
  rewrite /w rho_Dade_reciprocity; last by [].
  by rewrite linear_sub /= pf72a // subrr cfdot0r.
move: (ortho); rewrite cfdotC => /eqP; rewrite conjC_eq0 => /eqP ortho2.
have <-: '[w]_G = '[chi^\rho]_L by rewrite Dade_isometry //.
rewrite -{1 2}(subrK w chi).
set v := chi - w in ortho ortho2 *.
rewrite cfdotDl 2!cfdotDr ortho ortho2 addr0 add0r.
apply/leCifP; case eq: (_ == _); move/eqP: eq => eq.
  by rewrite /v eq subrr cfdot0l add0r.
rewrite ltCE -leC_sub -addrA subrr addr0 cfnorm_posC andbT.
apply/eqP => hyp; apply: eq.
rewrite -{2}['[w]_G]add0r in hyp; move/addIr/eqP: hyp.
by rewrite cfnorm_eq0 /v subr_eq0 => /eqP.
Qed.

(* 7.3 *)
Lemma pf73 chi :
  '[chi^\rho] <= #|G|%:R^-1 * (\sum_(g \in Atau) `|chi g| ^+ 2)
     ?= iff (forallb a, (a \in A) ==> (forallb u, (u \in H a) ==>
                        (chi (u * a)%g == chi a))).
Proof.
have nsAtauG: Atau <| G by rewrite /normal Dade_support_sub ?Dade_support_norm.
pose chi1 := chi * '1_Atau; set RHS := _ * _.
have inA1 a x: a \in A -> x \in H a -> (x * a)%g \in Dade_support1 ddA a.
  by move=> Aa Hx; rewrite (subsetP (sub_class_support _ _)) // mem_mulg ?set11.
have chi1E a x: a \in A -> x \in H a -> chi1 (x * a)%g = chi (x * a)%g.
  move=> Aa Ha_x; rewrite cfunE cfuniE // mulr_natr mulrb.
  by case: bigcupP => // [[]]; exists a; rewrite ?inA1.
have ->: chi^\rho = chi1^\rho.
  apply/cfunP => a; rewrite !cfunElock; case: ifP => // Aa; congr (_ * _).
  by apply: eq_bigr => x /chi1E->.
have Achi1: chi1 \in 'CF(G, Atau).
  by apply/cfun_onP=> x ?; rewrite cfunE (cfun_onP (cfuni_on _ _)) ?mulr0.
have{Achi1 RHS} <-: '[chi1] = RHS.
  rewrite (cfnormE Achi1); congr (_ * _).
  by apply: eq_bigr => x Atau_x; rewrite cfunE cfuniE // Atau_x mulr1.
congr (_ <= _ ?= iff _): (pf72b chi1).
apply/eqP/forall_inP=> [chi1id a Aa| chi_id].
  apply/forall_inP => x Ha_x; rewrite -{2}[a]mul1g -!chi1E // chi1id mul1g.
  by rewrite (DadeE _ Aa) ?inA1 ?Dade_id.
apply/cfunP => g; rewrite cfunE cfuniE // mulr_natr mulrb.
case: ifPn => [/bigcupP[a Aa] | /(cfun_onP (Dade_cfunS _ _))-> //].
case/imset2P=> _ z /rcosetP[x Ha_x ->] Gz ->{g}; rewrite !cfunJ {z Gz}//.
have{chi_id} chi_id := eqP (forall_inP (chi_id a Aa) _ _).
rewrite chi_id // (DadeE _ Aa) ?inA1 {x Ha_x}// cfunElock Aa.
rewrite (eq_bigr (fun _ => chi a)) => [|x Hx]; last by rewrite chi1E ?chi_id.
by rewrite sumr_const -[chi a *+ _]mulr_natl mulKf ?neq0GC.
Qed.

End PF71_73.


(*************************************)
(* 7.4 & 7.5 *)
Section PF74_75.

(* 7.4 *)
Variable m : nat.

Variable A : m.-tuple {set gT}.
Variable L : m.-tuple {group gT}.
Variable H : m.-tuple (gT -> {group gT}).

Hypothesis ddI : forall i, Dade_hypothesis G (tnth L i) (tnth H i) (tnth A i).

Local Notation "alpha ^\tau_ i" := (Dade (ddI i) alpha)
  (at level 2, format "alpha ^\tau_ i").

Local Notation "''Atau_' i" := (Dade_support (ddI i))
  (at level 2, format "''Atau_' i").

Local Notation "alpha ^\rho_ i" := (rho_fun (ddI i) alpha)
  (at level 2, format "alpha ^\rho_ i").

Hypothesis disjointA : forall i j, i != j -> [disjoint 'Atau_i & 'Atau_j].

Local Notation G0 := (gval G :\: \bigcup_(i < m) 'Atau_i).

(* 7.5 *)
Lemma pf75 (r : Iirr G) : 
  #|G|%:R ^-1 * ((\sum_(g \in G0) `|'chi_r g| ^+ 2) - #|G0|%:R)
    + \sum_i ('[('chi_r)^\rho_i] - #|tnth A i|%:R / #|tnth L i|%:R) <= 0.
Proof.
rewrite mulr_subr sumr_sub /=; set X := _ * _; set Y := \sum_i _.
pose f j i := #|G|%:R^-1 * \sum_(g \in 'Atau_i) `|'chi[G]_j g| ^+ 2.
have F1 j: 1 = #|G|%:R^-1 * (\sum_(g \in G0) `|'chi_j g| ^+ 2) + \sum_i f j i.
  rewrite -{1}(cfnorm_irr j) mulr_sumr -mulr_addr; congr (_ * _).
  rewrite -partition_disjoint_bigcup //=; set Atau := \bigcup_i _.
  rewrite addrC (big_setID Atau) (setIidPr _).
    by congr (_ + _); apply: eq_bigr => x _; rewrite normCK.
  by apply/bigcupsP=> i _; exact: Dade_support_sub.
have leYf: Y <= \sum_i f r i.
  by rewrite -leC_sub -sumr_sub posC_sum // => i _; rewrite leC_sub pf73.
have <-: \sum_i f 0 i = \sum_i #|tnth A i|%:R / #|tnth L i|%:R.
  apply: eq_bigr => i _.
  have [/subsetD1P[sAL _] /subsetIP[_ nAL] _ defCA _] := ddI i.
  transitivity '[1^\rho_i].
    apply/esym/eqP; rewrite /f chi0_1 pf73.
    apply/forall_inP=> a Aa; apply/forall_inP=> x Hx.
    rewrite !cfun1E groupMl // (subsetP _ x Hx) {x Hx}//.
    by have /sdprodP[_ /mulG_sub[/subsetIP[-> _] _] _ _] := defCA a Aa.
  rewrite mulrC rho_1 (cfnormE (cfuni_on _ _)); congr (_ * _).
  rewrite -sumr_const; apply: eq_bigr => a Aa.
  by rewrite cfuniE /normal ?sAL // Aa normC1 exp1rn.
rewrite -addrA (addrCA _ Y) -oppr_add addrA -posC_opp oppr_sub leC_sub.
apply: (@leC_trans 1); first by rewrite (F1 r) leC_add2l.
rewrite {1}(F1 0) (eq_bigr (fun _ => 1)) ?sumr_const ?leC_refl // => x.
by case/setDP=> Gx _; rewrite chi0_1 cfun1E Gx normC1 exp1rn.
Qed.

End PF74_75.

(* Hypothesis 7.6 and the proofs of 7.7 and 7.8 *)
Section PF76_78.

(* In this section, A = K^# with K <| L *)
Variables (K L : {group gT}) (H : gT -> {group gT}).
Let zi := seqIndT K L.
Let A := K^#.

Hypothesis ddA : Dade_hypothesis G L H A.
Hypothesis nKL : K <| L.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

Local Notation Atau := (Dade_support ddA).

Local Notation "alpha ^\rho" := (rho_fun ddA alpha)
  (at level 2, format "alpha ^\rho").

Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sKL : K \subset L. Proof. by move/andP: nKL => []. Qed.

Let k := #|K|%:R : algC.
Let e := #|L : K|%:R : algC.

Let unit_k : k != 0. Proof. exact: neq0GC. Qed.
Let unit_e : e != 0. Proof. exact: neq0GiC. Qed.
Let ke : k * e = #|L|%:R.
Proof. by apply/eqP; rewrite -natr_mul -eqN_eqC LaGrange. Qed.

Let n := size zi.
Let in_zi (i : 'I_n) : zi`_i \in zi. Proof. exact: mem_nth. Qed.


(********************)
(* 7.7 *)
Section PF77.

Variable zi0 : 'CF(L).
Hypothesis zi0_in_zi : zi0 \in zi.

Variable chi : 'CF(G).

Let d (f : 'CF(L)) := f 1%g / zi0 1%g.

Let zi_val1 (f : 'CF(L)) : f (1%g) = d f * zi0 (1%g).
Proof. by rewrite -mulrA mulVf ?(seqInd1_neq0 _ zi0_in_zi) ?mulr1. Qed.

Let c (f : 'CF(L)) := '[(f - d f *: zi0)^\tau, chi]_G.

Let crestr1 (X : {group gT}) (S : {set gT}) (f : 'CF(X)) :
  exists h, [/\ f \in 'CF(X, S) -> h \in 'CF(X, S^#),
    {in S^#, f =1 h} & {in 'CF(X, S^#), forall psi, '[psi, f] = '[psi, h]}].
Proof.
pose h := f - (f 1%g) *: '1_(1%g).
exists h.
have h_eq : {in S^#, f =1 h}.
  move => x; rewrite !inE !cfunE cfuniE ?normal1 // => /andP [x_n_1 xS].
  by rewrite inE (negPf x_n_1) mulr0 subr0.
split => //.
  rewrite !cfun_onE => supp_f.
  apply/subsetP => x; apply: contraR; rewrite !inE !cfunE negb_and negbK.
  rewrite cfuniE ?normal1 // inE.
  case x1: (x == _); rewrite (orTb, orFb) ?(eqP x1) ?mulr1 ?subrr //.
  by move => xnS; rewrite (supportP supp_f _ xnS) mulr0 subr0.
move => psi psiC /=.
rewrite !(cfdotEl _ psiC); congr (_ * _).
by apply: eq_bigr => x xS1; rewrite h_eq.
Qed.

(* 7.7(a) *)
Lemma pf77a x :
  x \in A -> (chi^\rho) x = \sum_(f <- zi) (c f)^* / '[f] * f x.
Proof.
move/andP: (nKL) => [_] sLNK xA.
pose psi (f : 'CF(L)) := f - d f *: zi0.
have psiC f: f \in zi -> psi f \in 'CF(L, A).
  move => f_zi; rewrite cfun_onE.
  apply/subsetP => g; rewrite inE /=; apply: contraR.
  rewrite inE negb_and negbK in_set1 !cfunE.
  case/orP => [| gnK]; first by move/eqP ->; rewrite zi_val1 subrr.
  suff [-> ->]: f g = 0 /\ zi0 g = 0 by rewrite mulr0 subrr.
  by rewrite (cfun_onP (seqInd_on _ f_zi)) ?(cfun_onP (seqInd_on _ zi0_in_zi)).
have f_eq f: f \in 'CF(L, A) -> f = e^-1 *: 'Ind[L] ('Res[K] f).
  move => fC; apply/cfunP => g; rewrite cfunE.
  case: (boolP (g \in K)) => gK; last first.
    rewrite !(cfun_on0 _ gK) ?mulr0 ?cfInd_normal //.
    by apply: (cfun_onS _ fC); exact: subD1set.
  rewrite cfIndE // -/k.
  set S := \sum_(y \in _) _.
  have {S}->: S = \sum_(y \in L) f g.
    apply: eq_bigr => u uL.
    rewrite cfResE //; first by exact: cfunJ.
    by rewrite memJ_norm //; move/subsetP: sLNK => /(_ u uL).
  rewrite sumr_const mulrA -invf_mul [e * k]mulrC ke.
  by rewrite -[f g *+ _]mulr_natl mulrA mulVf ?mul1r // neq0GC.
have {f_eq} f_in_zi f: f \in 'CF(L, A) -> f \in (\sum_(g <- zi) g%:VS)%VS.
  move => fC; rewrite (f_eq f fC).
  rewrite (cfun_sum_cfdot ('Res[K] f)).
  apply: memvZl; rewrite linear_sum /=; apply: memv_suml => r _.
  rewrite linearZ /=; apply: memvZl.
  rewrite (big_nth 0) big_mkord.
  apply/memv_sumP.
  have: exists j : 'I_n, 'Ind[L] 'chi_r = zi`_j.
    have: 'Ind[L] 'chi_r \in zi by apply/seqIndP; exists r.
    by case/(nthP 0) => j j_lt_n j_ind; exists (Ordinal j_lt_n); rewrite j_ind.
  case => i ->.
  exists (fun j => if j == i then zi`_i else 0); split.
    move => j _; case ji: (_ == _); last by exact: mem0v.
    by move/eqP: ji ->; exact: memv_inj.
  by rewrite -big_mkcond big_pred1_eq.
have {f_in_zi} f_in_psi f: f \in 'CF(L, A) -> 
                           exists f_, f = \sum_(i < n) (f_ i *: psi zi`_i).
  move => fC; have := f_in_zi f fC.
  rewrite (big_nth 0) big_mkord; case/memv_sumP => fv [fv_def f_sum].
  have: exists f_, forall i, fv i = f_ i *: zi`_i.
    exists (fun i => (fv i (1%g)) / zi`_i 1%g) => i.
    have:= fv_def  i => /(_ isT).
    case/injvP => fc ->; congr (_ *: _).
    by rewrite cfunE -mulrA mulfV ?mulr1 // (seqInd1_neq0 nKL (in_zi _)).
  case => f_ f_def; exists f_.
  have ->: \sum_(i < n) f_ i *: psi zi`_i = 
       \sum_(i < n) f_ i *: zi`_i - (\sum_(i < n) f_ i * d zi`_i) *: zi0.
    rewrite scaler_suml -sumr_sub.
    by apply: eq_bigr => i _; rewrite scaler_subr scalerA.
  suff ->: \sum_(i < n) f_ i * d zi`_i = 0.
    by rewrite scale0r subr0 f_sum; apply: eq_bigr => i _; exact: f_def.
  have: (\sum_(i < n) f_ i * d zi`_i) * zi0 1%g = f 1%g.
    rewrite -mulr_suml f_sum sum_cfunE.
    by apply: eq_bigr => i _; rewrite -mulrA -zi_val1 f_def cfunE.
  rewrite (cfun_on0 fC); last first.
    by rewrite in_setD1 negb_and negbK eqxx orTb.
  move/eqP; rewrite mulf_eq0; move: (seqInd1_neq0 nKL zi0_in_zi).
  by case: (zi0 _ == 0); first by []; rewrite orbF => _ /eqP.
have {f_in_psi}f_eq0 f: f \in 'CF(L, A) ->
  (forall g, g \in zi -> '[psi g, f]_L = 0) -> f = 0.
  move => fC prod0; have := f_in_psi f fC; case => f_ f_sum.
  apply/eqP; rewrite -cfnorm_eq0.
  rewrite {2}f_sum raddf_sum big1 //= => i _.
  by rewrite cfdotZr cfdotC prod0 ?in_zi // conjC0 mulr0.
pose b (f : 'CF(L)) := (c f)^* / '[f]_L.
have b0 : b zi0 = 0.
  by rewrite /b/c/d mulfV ?(seqInd1_neq0 _  zi0_in_zi) //
    scale1r subrr linear0 cfdot0l conjC0 mul0r.
pose f := chi^\rho - \sum_(g <- zi) b g *: g.
have fC : f \in 'CF(L, K).
  apply: memv_sub; last first.
    rewrite big_seq_cond; apply: memv_suml => g /andP [g_zi _].
    by apply: memvZl; exact: seqInd_on g_zi.
  by apply: cfun_onS (rho_cfunS ddA _); exact: subD1set.
case: (crestr1 K f) => h [] hC /(_ x xA) f_eq_h h_inner; move: f_eq_h.
suff ->: h = 0.
  rewrite !cfunE => /eqP; rewrite addr_eq0 opprK => /eqP ->.
  by rewrite sum_cfunE; apply: eq_bigr => i _; rewrite cfunE.
apply: (f_eq0 _ (hC fC)) => g g_zi.
rewrite -h_inner ?psiC // cfdot_subr.
have ->: '[psi g, chi^\rho]_L = c g by rewrite -rho_Dade_reciprocity // psiC.
rewrite cfdot_subl !cfdot_sumr (bigD1_seq _ g_zi) ?seqInd_uniq //=.
rewrite !big1_seq => [ | ff /andP[_ ff_zi] | ff /andP[ff_n_g ff_zi]].
- rewrite /b cfdotZr rmorphM fmorphV {1}cfdotC !conjCK subr0 addr0.
  by rewrite divfK (subrr, cfnorm_seqInd_neq0 nKL g_zi).
- have [<-| neq_zi0_ff] := eqVneq zi0 ff; first by rewrite b0 scale0r cfdot0r.
  by rewrite cfdotZr cfdotZl (seqInd_ortho nKL zi0_in_zi) ?mulr0.
by rewrite cfdotZr (seqInd_ortho nKL g_zi) ?mulr0 // eq_sym.
Qed.

Lemma pf77b :
  '[chi^\rho]
    = \sum_(f <- zi) \sum_(g <- zi)
         (c f)^* * c g / '[f] / '[g] * ('[f, g] - f 1%g * g 1%g / (e * k)).
Proof.
rewrite (cfnormE (rho_cfunS ddA _)) -ke.
have ->: \sum_(x \in A) `|chi^\rho x| ^+ 2 =
  \sum_(x \in A) (\sum_(i < n) \sum_(j < n) (c zi`_i)^* * (c zi`_j) / 
    '[zi`_i, zi`_i]_L / '[zi`_j, zi`_j]_L * (zi`_i x * (zi`_j x)^*)).
  apply: eq_bigr => x xA; rewrite (pf77a xA) (big_nth 0) big_mkord.
  rewrite normCK rmorph_sum big_distrlr /=.
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  rewrite [(_ / _ * _)^*]rmorphM [(_ / _)^*]rmorphM conjCK.
  rewrite fmorphV // -[in X in (_ / X * _^*)]cfdotC.
  set X := _ ^-1; set Y := _ ^-1; set C1 := _^*; set C2 := c zi`_j.
  rewrite (mulrAC C1 C2 X) 2!mulrA; congr (_ * _).
  by rewrite mulrA (mulrAC (C1 * X) _ _) (mulrAC (C1 * X * C2) _ _).
have ke_unit: k * e != 0 by exact: mulf_neq0.
rewrite -[X in _ = X]mul1r -(mulVf ke_unit) -[X in _ = X]mulrA; congr (_ * _).
rewrite -mulr_sumr (big_nth 0) big_mkord exchange_big /=; apply: eq_bigr => i _.
rewrite -mulr_sumr (big_nth 0) big_mkord exchange_big /=; apply: eq_bigr => j _.
rewrite mulr_sumr.
rewrite (mulrCA (k * e) _ _); congr (_ * _).
rewrite mulr_addr mulrN [e * k]mulrC.
rewrite (mulrCA (k * e) _ (_ ^-1)) mulfV // mulr1.
set X := \sum_(x \in _) _; set Y := _ * _ 1%g.
suff ->: k * e * '[zi`_i, zi`_j]_L = Y + X by rewrite addrAC subrr add0r.
rewrite (cfdotEl _ (seqInd_on nKL (in_zi i))) -ke.
rewrite mulrA mulfV // mul1r.
rewrite (big_setID 1%g) /= setIg1 big_set1 -/X /Y.
congr (_ * _ + _).
rewrite posC_conjK //; apply: (@char1_pos _ L _).
case/seqIndP: (in_zi j) => r _ ->.
by apply: cfInd_char; rewrite ?sKL ?irr_char.
Qed.


End PF77.


(*************************)

(* 7.8 *)

Section PF78.

Variable nu : {additive 'CF(L) -> 'CF(G)}.
(* This corresponds to zi \in Iirr L, zi \in calS *)
Variable r : Iirr L.

Local Notation calS := (seqIndD K L K 1).
Local Notation beta := ('Ind[L, K] 1 - 'chi_r)^\tau.

Hypothesis Schi : 'chi_r \in calS.
Hypothesis chi1 : 'chi_r 1%g = e.

(* Coherence hypotheses *)
Hypothesis S_non_trivial : exists2 theta, theta \in 'Z[calS, A] & theta != 0.
Hypothesis nu_isom : {in 'Z[calS] &, isometry nu}.
Hypothesis nu_to : {in 'Z[calS], forall phi, nu phi \in 'Z[irr G]}.
Hypothesis nu_tau : {in 'Z[calS, A], nu =1 Dade ddA}.

Let defCa : {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}.
Proof. by case: ddA. Qed.
Let coHL : {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.
Proof. by case: ddA. Qed.
Let nsHC : {in A, forall a, H a <| 'C_G[a]}.
Proof. by move=> a /defCa/sdprod_context[]. Qed.
Let sHG : {in A, forall a, H a \subset G}.
Proof. by move=> a /nsHC/normal_sub/subsetIP[]. Qed.

Let zi_distinct (i j : 'I_n) : i != j -> zi`_i != zi`_j.
Proof. by rewrite nth_uniq ?seqInd_uniq. Qed.

(* The consequence of coherence and that A = K^# *)
Let sizeS : (1 < size calS)%N.
Proof.
case: S_non_trivial => f fZ fn0.
case: (ltngtP (size calS) 1) => //.
  rewrite -addn1 -{2}[1%N]addn1 leq_add2r leqn0 size_eq0 => /eqP S_nil.
  move/vchar_span: fZ; rewrite S_nil span_nil memv0 => /eqP f0.
  by move: fn0; rewrite f0 eqxx.
case S: calS => [| g t] //=.
rewrite -addn1 -{2}[1%N]addn1 => /addIn /eqP; rewrite size_eq0 => /eqP t_nil.
move/vchar_span: (fZ); rewrite S t_nil span_seq1.
case/injvP => a f_ag; move/cfunP/(_ 1%g): (f_ag); rewrite cfunE.
rewrite (supportP (support_vchar fZ)); last first.
  by rewrite !inE negb_and negbK eqxx orTb.
move/esym => /eqP; rewrite mulf_eq0; case/orP.
  by move/eqP => a0; move: f_ag fn0; rewrite a0 scale0r => ->; rewrite eqxx.
have: g \in calS by rewrite S inE eqxx orTb.
by move/seqInd1_neq0/negPf->.
Qed.

(*
Lemma raddfMZ z f : isIntC z -> nu (z *: f) = z *: nu f.
Proof.
rewrite isIntCE; case/orP; case/isNatCP => m.
  by move ->; rewrite !scaler_nat raddfMn.
move/eqP; rewrite eqr_oppC => /eqP ->.
by rewrite !scaleNr !scaler_nat raddfMNn.
Qed.
*)

Lemma pf78a1 f : f \in calS -> '[nu f, 1] = 0.
Proof.
move => fS.
have eq_g g : g \in calS -> '[nu (g - (g 1%g / e) *: 'chi_r), 1]_G = 0.
  move => gS; rewrite nu_tau; last by exact: seqInd_sub_lin_vchar.
  rewrite rho_Dade_reciprocity ?(seqInd_sub_lin_on _ Schi) // rho_1.
  set mu := _ - _.
  have ->: '[mu, '1_A] = '[mu, 1].
    rewrite !(cfdotEl _ (seqInd_sub_lin_on nKL Schi chi1 gS)).
    congr (_ * _); apply: eq_bigr => x xK1.
    move: (xK1); rewrite inE => /andP [_] xK.
    by rewrite cfuniE ?xK1 ?cfun1E ?(subsetP sKL) // /normal sAL nAL.
  rewrite cfdot_subl cfdotZl.
  by rewrite !((seqInd_ortho_1 nKL) K 1%G) // mulr0 subrr.
suff {f fS}: '[nu 'chi_r, 1] = 0.
  move => eq0; have := eq_g f fS.
  rewrite raddf_sub (raddfZ_NatC _ _ (dvd_index_seqInd1 _ fS)) //.
  by rewrite cfdot_subl cfdotZl eq0 mulr0 subr0.
have norm_chi1 : '[nu 'chi_r, nu 'chi_r]_G = 1.
  by rewrite nu_isom ?cfdot_irr ?eqxx ?seqInd_vcharW.
have chi_irr := vchar_norm1P (nu_to (seqInd_vcharW nKL Schi)) norm_chi1.
case: chi_irr => e0 [] rr; set eps := _ ^+ _; move => chi_eq.
rewrite chi_eq cfdotZl.
case r0: (rr == 0); last first.
  by rewrite -chi0_1 cfdot_irr r0 mulr0.
have [f fS chi_n_f]: exists2 f, f \in calS & 'chi_r != f.
  pose S := rem 'chi_r calS; pose xi := S`_0.
  have: xi \in S by rewrite mem_nth // size_rem // -subn1 subn_gt0.
  rewrite [S]rem_filter ?seqInd_uniq ?mem_filter //= eq_sym => /andP[].
  by exists xi.
have prod0: '[nu f, 1] = 0.
  rewrite -chi0_1 -(eqP r0) -(canLR (signrZK _) chi_eq) -/eps cfdotZr.
  by rewrite nu_isom ?seqInd_vcharW // (seqInd_ortho nKL fS) ?mulr0 // eq_sym.
have/eqP := eq_g f fS.
rewrite raddf_sub (raddfZ_NatC _ _ (dvd_index_seqInd1 _ fS)) // cfdot_subl.
rewrite subr_eq0 prod0 eq_sym chi_eq !cfdotZl mulf_eq0 orbC => /predU1P[] //.
by case/idPn; rewrite mulf_neq0 ?invr_eq0 ?(seqInd1_neq0 nKL fS).
Qed.

(* 7.8(a)-2 *)

Local Notation mu := ('Ind[_, gval K] 1 - 'chi_r).
Let mu_vchar : mu \in 'Z[irr L, A] := cfInd1_sub_lin_vchar nKL Schi chi1.
Let mu_on : mu \in 'CF(L, A):= vchar_on mu_vchar.

Lemma dot_beta_1 : '[beta, 1] = 1.
Proof.
rewrite rho_Dade_reciprocity // rho_1.
have ->: '[mu, '1_A] = '[mu, 1].
  rewrite !(cfdotEl _ mu_on); congr (_ * _); apply: eq_bigr => x Ax.
  by rewrite cfun1E (subsetP sAL) // cfuniE ?Ax //; exact/andP.
rewrite cfdot_subl -Frobenius_reciprocity (seqInd_ortho_1 _ _ Schi) // subr0.
by rewrite cfRes_cfun1 // cfnorm1.
Qed.

Lemma pf78a2 : exists a, exists Gamma,
  [/\ isIntC a, 
    '[Gamma, 1]_G = 0, 
    {in calS, forall f, '[Gamma, nu f] = 0} &
    beta = Gamma + 1 - nu 'chi_r + 
           a *: (\sum_(f <- calS) (f 1%g / e / '[f]) *: nu f)].
Proof.
exists ('[beta, nu 'chi_r]_G + 1).
exists (beta - '[beta, 1] *: 1 - 
         \sum_(f <- calS) ('[beta, nu f] / '[f]) *: nu f).
split.
- apply: isIntC_add (isIntC_nat 1).
  apply: cfdot_vchar_Int; last by apply: nu_to; exact: seqInd_vcharW.
  exact: Dade_vchar.
- rewrite !cfdotDl !cfdotNl cfdotZl cfnorm1 mulr1 subrr.
apply/eqP; rewrite subr_eq0 eq_sym; apply/eqP.
  rewrite cfdot_suml big1_seq //.
  move => f /andP [_] fS.
  by rewrite cfdotZl (pf78a1 fS) mulr0.
- move => f fS /=.
  rewrite !cfdotDl !cfdotNl cfdotZl.
  rewrite ['[1, _]_G]cfdotC (pf78a1 fS) conjC0 mulr0 subr0.
  apply/eqP; rewrite subr_eq0 eq_sym; apply/eqP; rewrite cfdot_suml.
  rewrite (bigD1_seq f) ?seqInd_uniq //= big1_seq; last first.
    move=> g /andP[gnf gS]; rewrite cfdotZl nu_isom ?(seqInd_vcharW nKL) //.
    by rewrite (seqInd_ortho _ gS fS gnf) // mulr0.
  rewrite addr0 cfdotZl nu_isom ?seqInd_vcharW //.
  by rewrite divfK // (cfnorm_seqInd_neq0 nKL fS).
set SG := \sum_(_ <- _) _.
set S := (_ + _) *: _.
rewrite dot_beta_1 scale1r [_ - _ - _]addrAC.
rewrite -[_ - 1 + _]addrA [- _ + _]addrC subrr addr0.
rewrite -!addrA -{1}[beta]addr0; congr (_ + _).
rewrite addrC; apply/eqP; rewrite eq_sym subr_eq0 eq_sym; apply/eqP.
rewrite /S /SG !(bigD1_seq _ Schi) ?seqInd_uniq //=.
rewrite scaler_addr addrA; congr (_ + _).
  rewrite chi1 (mulfV unit_e) cfnorm_irr !divr1 scaler_addl !scale1r.
  by rewrite addrCA addrA subrK.
rewrite scaler_sumr big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP [fS f_n_chi].
rewrite scalerA !mulrA; congr ((_ / _) *: _).
have: '[beta, nu (f - f 1%g / e *: 'chi_r)] = f 1%g / e.
  set c := _ / _.
  rewrite nu_tau ?seqInd_sub_lin_vchar //.
  rewrite Dade_isometry ?(seqInd_sub_lin_on _ Schi) //.
  rewrite !cfdot_subl !cfdot_subr !cfdotZr cfdotC cfnorm_irr mulr1.
  rewrite (seqInd_ortho_Ind1 _ _ fS) // conjC0 sub0r.
  rewrite (seqInd_ortho _ Schi fS) //; last by rewrite eq_sym.
  rewrite cfdotC (seqInd_ortho_Ind1 _ _ Schi) // conjC0.
  by rewrite mulr0 oppr0 !add0r opprK isNatC_conj ?(dvd_index_seqInd1 _ fS).
rewrite [nu _]raddf_sub raddfZ_NatC ?(dvd_index_seqInd1 _ fS) // cfdot_subr.
move/eqP; rewrite subr_eq => /eqP ->.
rewrite -mulrA mulr_addl mul1r addrC cfdotZr mulrC.
by congr (_ * _ + _); apply: isNatC_conj; exact: (dvd_index_seqInd1 _ fS).
Qed.

(*********************************)
(* 7.8(b) *)

Hypothesis ineq : e <= (k - 1) / 2%:R.

Let u := e^-1 * (1 - k^-1).
Let v := k^-1.
Let w := 1 - e / k.

Let ineq1 a : isIntC a -> 0 <= u * a ^+ 2 - 2%:R * v * a.
Proof.
move => aZ.
have k_gt0: 0 < k := sposGC K.
have e_gt0: 0 < e := sposGiC L K.
have u_ge0: 0 <= u.
  rewrite posC_mul ?posC_inv ?posC_nat // leC_sub.
  by rewrite -(leC_pmul2l _ _ k_gt0) mulr1 divff // -(leq_leC 1) cardG_gt0.
have vu: 2%:R * v <= u.
  rewrite -leC_sub /u /v.
  rewrite -(posC_mulr _ k_gt0) mulr_subr mulrCA mulr_subr mulrCA mulfV // !mulr1.
  rewrite -(posC_mulr _ e_gt0) mulr_subr mulrA mulfV // mul1r mulrC.
  move: ineq; have two_gt0: 0 < 2%:R by rewrite -(ltn_ltC 0).
  rewrite -leC_sub -(posC_mulr _ two_gt0) mulr_subr mulrCA mulfV ?mulr1 //.
  by rewrite -neq0N_neqC.
move: aZ; rewrite expr2 mulrA -mulr_subl isIntCE.
case a0: (a == 0); first by move/eqP: a0 ->; rewrite mulr0 leC_refl.
case/orP; case/isNatCP => t.
  move => ta; move: ta a0 -> => a0; apply: posC_mul; last by exact: posC_nat.
  rewrite leC_sub; apply: (leC_trans vu); rewrite -leC_sub.
  rewrite -{2}[u]mulr1 -mulr_subr; apply: posC_mul; first by [].
  rewrite leC_sub -(leq_leC 1).
  by case: (ltnP 0 t) => //; rewrite leqn0 eqN_eqC a0.
move => ta; move: a0; rewrite -mulrNN -eqr_opp oppr0 ta oppr_sub => a0.
apply: posC_mul; last by exact: posC_nat.
apply: posC_add.
  apply: posC_mul; first by rewrite -(leq_leC 0).
  by rewrite posC_inv posC_nat.
by rewrite -mulrN ta posC_mul // posC_nat.
Qed.


(* 7.8(b) Part 1 *)

Lemma pf78b1 : w <= '[(nu 'chi_r)^\rho].
Proof.
pose a := '[beta, nu 'chi_r]_G + 1.
have aZ: isIntC a.
  rewrite isIntC_add ?(isIntC_nat 1) ?cfdot_vchar_Int ?nu_to ?seqInd_vcharW //.
  by rewrite Dade_vchar ?(pre_beta_vchar _ Schi).
pose z0 := (filter (predC1 'chi_r) calS)`_0.
pose c (f : 'CF(L)) := '[(f - f 1%g / z0 1%g *: z0)^\tau, nu 'chi_r]_G.
have z0_in : z0 \in filter (predC1 'chi_r) calS.
  rewrite /z0 -rem_filter ?seqInd_uniq //.
  by apply: mem_nth; rewrite size_rem // -(subnK sizeS) addn2.
have z0S : z0 \in calS by move: z0_in; rewrite mem_filter => /andP [].
have z0_n_chi : z0 != 'chi_r by move: z0_in; rewrite mem_filter => /andP [] /=.
have z01_neq0 : z0 1%g != 0 by rewrite (seqInd1_neq0 nKL z0S).
have c0 : c z0 = 0 by rewrite /c mulfV // scale1r subrr linear0 cfdot0l.
have c1 : c ('Ind[L, K] 1) = a.
  transitivity ('[beta + ('chi_r - 'Ind[L, K] 1 1%g / z0 1%g *: z0)^\tau, nu 'chi_r]_G).
    congr ('[_, _]_G); rewrite -linearD.
    by rewrite addrA -[_ - _ + _]addrA [- _ + _]addrC subrr addr0.
  apply: (mulfI z01_neq0).
  rewrite cfdotDl !mulr_addr; congr (_ + _).
  rewrite -cfdotZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
  rewrite /= -nu_tau ?nu_isom //
    ?cfInd_cfun1 ?cfunE ?cfuniE ?in_group ?mulr1 -/e -?chi1 //; first last.
  - exact: sub_seqInd_vchar.
  - exact: seqInd_vcharW.
  - exact: vcharW (sub_seqInd_vchar nKL Schi z0S).
  rewrite cfdot_subl !cfdotZl cfdot_irr eqxx.
  by rewrite (seqInd_ortho nKL z0S) ?mulr1 ?mulr0 ?subr0.
have c2 : c 'chi_r = 1.
  apply: (mulfI z01_neq0).
  rewrite /c -cfdotZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
  rewrite /= -nu_tau ?nu_isom ?['chi_r \in _]seqInd_vcharW //
    ?(@vcharW _ _ _ A) ?sub_seqInd_vchar //.
  rewrite cfdot_subl !cfdotZl cfdot_irr eqxx.
  by rewrite (seqInd_ortho nKL z0S) ?mulr0 ?mulr1 ?subr0.
have ci0 f : f \in zi -> f != 'Ind[L, K] 1 -> f != 'chi_r -> c f = 0.
  move => f_zi f_n_1 f_n_chi.
  have fS: f \in calS by rewrite [calS]seqIndC1_filter // mem_filter /= f_n_1.
  apply: (mulfI z01_neq0).
  rewrite /c -cfdotZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
  rewrite /= -nu_tau ?nu_isom ?['chi_r \in _]seqInd_vcharW //
    ?(@vcharW _ _ _ A) ?sub_seqInd_vchar //.
  rewrite cfdot_subl !cfdotZl.
  by rewrite !(seqInd_ortho nKL _ Schi) ?mulr0 ?subr0.
rewrite (pf77b (seqInd_subT z0S)).
pose pred12 := predU (pred1 ('Ind[L, K] 1)) (pred1 'chi_r).
rewrite (bigID pred12) /= addrC big1_seq ?add0r; last first.
  move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  apply: big1_seq => g /andP [_ g_zi].
  by move: (ci0 f f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite conjC0 !mul0r.
have sumU F f1 f2: f1 \in zi -> f2 \in zi -> f1 != f2 ->
     \sum_(i <- zi | (i == f1) || (i == f2)) (F i : algC) = F f1 + F f2.
  move => f1_zi f2_zi f1_n_f2.
  rewrite big_mkcond (bigD1_seq f1) ?seqInd_uniq ?eqxx //=; congr (_ + _).
  rewrite big_mkcond (bigD1_seq f2) ?seqInd_uniq ?eqxx ?orbT //= eq_sym f1_n_f2.
  by rewrite big1 ?addr0 // => f /negPf->; case: eqP.
have one_n_chi: 'Ind[L, K] 1 != 'chi_r.
  by move: Schi; rewrite eq_sym [calS]seqIndC1_filter // mem_filter => /andP[].
rewrite sumU // ?seqIndT_Ind1 ?(seqInd_subT Schi) //.
rewrite (bigID pred12) [in X in _ + X](bigID pred12) /=.
rewrite !sumU ?seqIndT_Ind1 ?(seqInd_subT Schi) //= !big1_seq; first last.
- move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  by move: (ci0 f f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite mulr0 !mul0r.
- move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  by move: (ci0 f f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite mulr0 !mul0r.
move: c1 c2; rewrite /c => -> ->; rewrite -/a.
rewrite cfdot_irr eqxx cfnorm_Ind_cfun1 // cfInd1 // -/e cfun1E group1 !mulr1.
rewrite cfdotC (seqInd_ortho_Ind1 _ _ Schi) // conjC0 conjC1.
rewrite invr1 !addr0 !sub0r !mul1r !mulr1 (isIntC_conj aZ) chi1.
rewrite !invf_mul !mulrA mulfK // -/w mulrN mulrA divfK //.
rewrite -{3}[e]mulr1 -mulr_subr mulrA divfK // -mulrA -/u -/v.
rewrite addrA -{1}[w]add0r leC_add2r -addrA -mulr2n -mulr_natl mulrN.
by rewrite mulrC [a * v]mulrC !mulrA -mulrA -expr2 ineq1.
Qed.

(* 7.8(b) Part 2 *)
Variable a : algC.
Variable Gamma : 'CF(G).

Hypothesis ortho_Gamma1 : '[Gamma, 1]_G = 0.
Hypothesis ortho_GammaS : {in calS, forall f, '[Gamma, nu f]_G = 0}.
Hypothesis beta_sum : beta = Gamma + 1 - nu 'chi_r + 
  a *: (\sum_(f <- calS) (f 1%g / e / '[f]_L) *: nu f).


Let a_eq : '[beta, nu 'chi_r]_G = a - 1.
Proof.
rewrite beta_sum !cfdotDl cfdotNl cfdotZl.
rewrite (ortho_GammaS Schi) cfdotC (pf78a1 Schi).
rewrite conjC0 !add0r nu_isom ?seqInd_vcharW // cfdot_irr eqxx addrC.
congr (_ - _); rewrite cfdot_suml (bigD1_seq 'chi_r) ?seqInd_uniq // big1_seq.
  rewrite cfdotZl chi1 (mulfV unit_e) cfdot_irr eqxx invr1 /= addr0.
  by rewrite nu_isom ?seqInd_vcharW // cfnorm_irr !mulr1.
move => f /andP [f_n_chi fS]; rewrite cfdotZl.
by rewrite nu_isom ?seqInd_vcharW // (seqInd_ortho nKL _ Schi f_n_chi) ?mulr0.
Qed.

Let isIntC_a : isIntC a.
Proof.
move/eqP: a_eq; rewrite eq_sym subr_eq => /eqP ->.
rewrite isIntC_add ?(isIntC_nat 1) ?cfdot_vchar_Int ?nu_to ?seqInd_vcharW //.
by rewrite Dade_vchar ?(pre_beta_vchar _ Schi).
Qed.


Lemma pf78b2 : '[Gamma] <= e - 1.
Proof.
have : '[beta] = e + 1.
  rewrite Dade_isometry ?(pre_beta_on _ Schi) //.
  rewrite cfdotDl !cfdotDr !cfdotNl !cfdotNr.
  rewrite cfnorm_Ind_cfun1 // cfdotC.
  rewrite (seqInd_ortho_Ind1 _ _ Schi) ?inE // conjC0.
  by rewrite cfdot_irr eqxx oppr0 sub0r addr0 -mulNrn mulr1n opprK.
rewrite beta_sum (bigD1_seq 'chi_r) ?seqInd_uniq //= -big_filter.
rewrite chi1 mulfV // cfnorm_irr divr1 scale1r scaler_addr addrA.
set v1 := _ + 1 + _ + _.
set v2 := a *: _.
rewrite cfnormD.
have ->: '[v1, v2] = 0.
  rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 //.
  move => f; rewrite mem_filter andTb => /andP [] f_n_chi fS.
  rewrite /= cfdotZr !cfdotDl cfdotZl cfdotNl.
  rewrite ortho_GammaS // nu_isom ?seqInd_vcharW //.
  apply/eqP; rewrite mulf_eq0; apply/orP; right.
  rewrite cfdotC pf78a1 // cfdotC (seqInd_ortho nKL fS) //.
  by rewrite conjC0 mulr0 !addr0 subr0.
rewrite conjC0 !addr0.
have ->: '[v1] = '[Gamma] + 1 + (a - 1) ^+ 2.
  rewrite /v1 -!addrA cfnormD.
  set x := '[Gamma, 1 + _]; have {x}->: x = 0.
    rewrite /x !cfdotDr !cfdotNr cfdotZr ortho_Gamma1.
    by rewrite ortho_GammaS // mulr0 addr0 subr0.
  rewrite -scaleN1r -scaler_addl cfnormD cfnorm1.
  set x := '[1, _]; have {x}->: x = 0.
    by rewrite [x]cfdotZr cfdotC pf78a1 // conjC0 mulr0.
  rewrite conjC0 !addr0; congr (_ + (_ + _)).
  rewrite cfnormZ int_normCK ?isIntC_add ?isIntC_opp ?(isIntC_nat 1) // addrC.
  by rewrite nu_isom ?seqInd_vcharW // cfdot_irr eqxx mulr1.
suffices ->: '[v2] = a ^+ 2 * (k * u - 1).
  rewrite expr2 !mulr_subr !mulr_subl !mulr1 !mul1r -expr2.
  rewrite addrAC !addrA subrK mulrCA oppr_add opprK => /eqP.
  rewrite eq_sym -!addrA -subr_eq oppr_add !addrA addrK => /eqP <-.
  rewrite leC_add2l leC_opp -leC_sub addrK -addrA -mulr2n -mulr_natl mulrN.
  rewrite -[2%:R](mulVKf unit_k) -/v (mulrC v) -(mulrA k) -(mulrC u) -mulr_subr.
  by rewrite posC_mul ?posC_nat ?ineq1.
rewrite cfdotZl cfdotZr (isIntC_conj isIntC_a) expr2 mulrA; congr (_ * _).
have norm_sum (s : seq 'CF(L)) (F : 'CF(L) -> 'CF(G)) :
  uniq s -> {in s &, forall f g, f != g -> '[F f, F g]_G = 0} ->
  '[\sum_(f <- s) F f, \sum_(f <- s) F f]_G = \sum_(f <- s) '[F f, F f]_G.
  move => uniq_s ortho_s.
  rewrite raddf_sum big_seq_cond [in X in _ = X]big_seq_cond /=.
  apply: eq_bigr => f /andP [] fS _; rewrite (bigD1_seq f) //=.
  rewrite cfdotDl; apply: canLR (addNKr _) _.
  rewrite addNr cfdot_suml big1_seq //=.
  by move => g /andP [] gS g_n_f; rewrite ortho_s.
rewrite norm_sum ?filter_uniq ?seqInd_uniq //; last first.
  move => f g; rewrite mem_filter => /andP [_] fS.
  rewrite mem_filter => /andP [_] gS f_n_g.
  rewrite cfdotZl cfdotZr nu_isom ?seqInd_vcharW //.
  by rewrite (seqInd_ortho nKL fS gS f_n_g) !mulr0.
do 2!apply: (mulfI unit_e); rewrite mulrA big_distrr /=.
rewrite mulr_subr mulr1 mulrCA mulVKf // (mulr_subr k) divff // mulr1 mulr_subr.
rewrite -sum_seqIndC1_square // (bigD1_seq _ Schi) ?seqInd_uniq //=.
rewrite cfnorm_irr divr1 chi1 addrC addKr -[rhs in _ = rhs]big_filter.
apply: eq_big_seq => phi; rewrite mem_filter => /andP[_ Sphi].
rewrite cfnormZ nu_isom ?seqInd_vcharW // normC_pos.
  rewrite !exprn_mull -[_ * '[phi]]mulrA divfK ?(cfnorm_seqInd_neq0 _ Sphi) //.
  by rewrite expr_inv mulrCA mulrA divfK // mulf_neq0.
rewrite !posC_mul ?posC_inv ?posC_nat ?cfnorm_posC //.
by rewrite posC_isNatC ?(seqInd1_Nat Sphi).
Qed.

(***************************************)
(* 7.8c *)

Lemma pf78c1 f :
    f \in irr G -> {in calS, forall psi, '[nu psi, f] = 0} ->
  {in A, forall x, f^\rho x = '[beta, f]}.
Proof.
move => f_irr f_ortho x xA.
have fZ: f \in 'Z[irr G] by case/irrP: f_irr => t ->; rewrite irr_vchar.
rewrite (pf77a (seqInd_subT Schi) _ xA).
rewrite (bigD1_seq ('Ind[L, K] 1)) ?seqInd_uniq ?seqIndT_Ind1 //=.
rewrite big1_seq ?addr0; last first.
  move => g /andP [g_n_1 g_zi].
  have gS: g \in calS by rewrite [calS]seqIndC1_filter // mem_filter /= g_n_1.
  rewrite chi1 -nu_tau ?seqInd_sub_lin_vchar // raddf_sub.
  rewrite raddfZ_NatC ?(dvd_index_seqInd1 _ gS) // cfdot_subl !cfdotZl.
  by rewrite !f_ortho // mulr0 subrr conjC0 !mul0r.
rewrite cfInd_cfun1 // !cfunE !cfuniE // in_group.
rewrite in_setD1 in xA; move/andP: xA => [_] ->.
rewrite mulr1 chi1 mulfV // scale1r.
rewrite -cfInd_cfun1 // cfnorm_Ind_cfun1 // divfK //.
by rewrite isIntC_conj // cfdot_vchar_Int // Dade_vchar.
Qed.

Lemma pf78c2 f : f \in irr G -> 
  (forall psi, psi \in calS -> '[nu psi, f]_G = 0) ->
  '[f^\rho]_L = #|A|%:R / #|L|%:R * '[beta, f]_G ^+ 2.
Proof.
move => f_irr f_ortho.
have fZ: f \in 'Z[irr G] by case/irrP: f_irr => t ->; rewrite irr_vchar.
rewrite (norm_chi_rho ddA).
rewrite [_ / _]mulrC -mulrA; congr (_ * _).
rewrite -sum1_card natr_sum -!mulr_suml; apply: eq_bigr => x xA.
rewrite pf78c1 // mul1r sqrtCK expr2; congr (_ * _).
by rewrite isIntC_conj ?cfdot_vchar_Int // Dade_vchar ?(pre_beta_vchar _ Schi).
Qed.

End PF78.

End PF76_78.

(******************************)
(* PF 7.9 *)

Section PF79.

Hypothesis oddG : odd #|G|.

Variable k : nat.
Variables (K L : k.-tuple {group gT}) (H : k.-tuple (gT -> {group gT})).
Variable nu : forall i, {additive 'CF(tnth L i) -> 'CF(G)}.
Variable r : forall i, Iirr (tnth L i).

Local Notation KK i := (tnth K i).
Local Notation LL i := (tnth L i).
Local Notation A i := (KK i)^#.
Local Notation calS i := (seqIndD (KK i) (LL i) (KK i) 1).
Local Notation e i := (#|gval (LL i) : gval (KK i)|%:R : algC).

Hypothesis ddI : forall i, Dade_hypothesis G (LL i) (tnth H i) (A i).

Local Notation "alpha ^\tau_ i" := (Dade (ddI i) alpha)
  (at level 2, format "alpha ^\tau_ i").

Local Notation Atau i := (Dade_support (ddI i)).

Let beta i := ('Ind[LL i, KK i] 1 - 'chi_(r i))^\tau_i.

Hypothesis disjointAtau : forall i j, i != j -> [disjoint Atau i & Atau j].
Hypothesis nKL : forall i, KK i <| LL i.

(* Coherence assumptions *)
Hypothesis S_non_trivial : forall i, 
  exists2 theta, theta \in 'Z[calS i, A i] & theta != 0.
Hypothesis nu_isom : forall i, {in 'Z[calS i] &, isometry (nu i)}.
Hypothesis nu_to : forall i, {in 'Z[calS i], forall phi, (nu i) phi \in 'Z[irr G]}.
Hypothesis nu_tau : forall i, {in 'Z[calS i, A i], nu i =1 Dade (ddI i)}.

Hypothesis Schi : forall i, 'chi_(r i) \in calS i.
Hypothesis chi1 : forall i, 'chi_(r i) 1%g = e i.


(************************************)

Let sAL i : A i \subset LL i. Proof. by have [/subsetD1P[]] := ddI i. Qed.
Let nAL i : LL i \subset 'N(A i). Proof. by have [_ /subsetIP[]] := ddI i. Qed.
Let sLG i : LL i \subset G. Proof. by have [_ /subsetIP[]] := ddI i. Qed.
Let sKL i : KK i \subset LL i. Proof. by move/andP: (nKL i) => []. Qed.


(**********************************)

Let d i := beta i - 1 + (nu i) 'chi_(r i).

Let d_conjC i : ((d i)^*)%CF = d i.
apply/eqP; rewrite -subr_eq0 /d.
rewrite rmorphD rmorph_sub /= cfConjC1 !oppr_add !addrA !subr_eq add0r.
rewrite addrAC [in X in _ == X]addrAC; apply/eqP; congr (_ - _).
apply/eqP; rewrite -subr_eq addrAC eq_sym -subr_eq eq_sym.
rewrite Dade_conjC ?pre_beta_memc ?chi1 ?Schi //.
rewrite -linear_sub rmorph_sub /= conj_cfInd cfConjC1.
rewrite addrAC oppr_add addrA subrr opprK add0r.
pose S := [:: 'chi_(r i); (('chi_(r i))^*)%CF].
have sSS : {subset S <= calS i} by apply/allP; rewrite /= cfAut_seqInd Schi.
have freeS: free S.
  have := seqInd_conjC_ortho2 (nKL i) (subxx _) (oddSg (sLG i) oddG) (Schi i).
  exact: orthonormal_free.
have sSZ X : {subset 'Z[S, X] <= 'Z[calS i, X]}.
  apply: vchar_subset => //; exact: seqInd_free.
rewrite (cfAut_Dade_ext _ (uniq_free freeS) _ _ _ _ (sub_in1 _ (@nu_tau i))) //.
- by rewrite -nu_tau ?raddf_sub // seqInd_sub_Aut_vchar ?Schi //.
- by apply/allP; rewrite /= -conjC_IirrE !irr_chi.
- move => f; rewrite vchar_split [in X in _ = X]vchar_split cfunD1E cfun_onD1.
  apply: andb_id2l => ZSf; rewrite (@vchar_on _ _ (calS i)) //.
  apply: (vchar_trans_on ((seqInd_vchar _) _)); last exact: sSZ.
  by rewrite /normal sKL -normD1 nAL.
- by apply/allP; rewrite /= cfConjCK !inE !eqxx orbT.
- split; [exact: sub_in2 (@nu_isom i) | exact: sub_in1 (@nu_to i)].
exact: mem_head.
Qed.

Let d_ortho1 i : '[d i, 1] = 0.
Proof.
rewrite !cfdotDl cfdotNl.
rewrite (dot_beta_1 (ddI i)) ?Schi ?chi1 //.
rewrite (@pf78a1 _ _ _ (ddI i) _ (nu i) (r i)) ?Schi //.
by rewrite cfnorm1 subrr addr0.
Qed.

Let beta12_ortho i j : i != j -> '[beta i, beta j] = 0.
Proof.
move => i_n_j.
rewrite (@cfdot_complement _ G (Atau i)) //.
  by rewrite Dade_cfunS ?pre_beta_memc.
have: beta j \in 'CF(G, Atau j) by rewrite Dade_cfunS ?pre_beta_memc.
rewrite cfun_onE [in X in _ -> X]cfun_onE => sA.
apply: (subset_trans sA).
by rewrite subsetD disjoint_sym (disjointAtau i_n_j) Dade_support_sub.
Qed.

Let nu_chi12_ortho i j : i != j -> '[(nu i) 'chi_(r i), (nu j) 'chi_(r j)]_G = 0.
Proof.
move => i_n_j.
pose S a := [:: (nu a) 'chi_(r a); (nu a) ((('chi_(r a))^*)%CF)].
have S_ortho a : orthonormal (S a).
  apply/orthonormal2P; rewrite ?memc_Zirr ?nu_to ?seqInd_vcharW ?seqIndC1_conjC //.
  split; rewrite nu_isom ?seqInd_vcharW ?cfAut_seqInd // ?cfdot_irr ?eqxx ?Schi //.
    by rewrite (seqInd_conjC_ortho (nKL a) _ _ (Schi a)) ?(oddSg (sLG a)).
  by rewrite cfdot_conjC cfdot_irr eqxx conjC1.
have sSZirr a : {subset S a <= 'Z[irr G]}.
  by move => f; rewrite 2!inE; case/orP => /eqP ->;
    rewrite nu_to ?seqInd_vcharW ?cfAut_seqInd ?Schi.
have/(_ 1 1) := vchar_pairs_orthonormal (conj (sSZirr i) (sSZirr j)).
rewrite !S_ortho nonzero1r (isIntC_Real (isIntC_nat 1)) /=.
rewrite !scale1r -!raddf_sub.
rewrite [(nu i) (_ - _)]nu_tau ?[(nu j) (_ - _)]nu_tau ?seqInd_sub_Aut_vchar ?Schi //.
rewrite !Dade1 eqxx.
set prod := '[_, _].
have ->: prod == 0.
  rewrite [prod](cfdotElr (Dade_cfunS _ _) (Dade_cfunS _ _)).
  by rewrite ((_ :&: _ =P set0) _) ?big_set0 ?mulr0 // setI_eq0 disjointAtau.
move => /(_ isT isT isT) /orthonormalP [] => uniq_abcd.
move => /(_ (nu i 'chi_(r i)) (nu j 'chi_(r j))); rewrite !inE !eqxx !orbT /=.
move => /(_ isT isT) ->; move: uniq_abcd => /=.
by rewrite !inE !negb_or => /andP [] /and3P [] => _ /negPf ->.
Qed.

Let dot_d12_even i j : exists2 a, isIntC a & '[d i, d j]_G = a + a.
Proof.
pose I0 := filter [pred xi | (xi^*)%CF == xi] (irr G).
pose I1 := map (tnth (irr G)) (filter [pred i : Iirr G | (i < conjC_Iirr i)%N] (enum (Iirr G))).
pose I2 := map (@cfAut gT _ conjC) I1.
have irr_uniq : uniq (irr G).
  by rewrite uniq_free ?(free_is_basis (irr_is_basis _)).
have I0_uniq : uniq I0 by exact: filter_uniq.
have I1_uniq : uniq I1.
  by rewrite map_inj_uniq ?filter_uniq -?enumT ?enum_uniq //; exact: chi_inj.
have I2_uniq : uniq I2.
  by rewrite map_inj_uniq //; apply: inv_inj; exact: cfConjCK.
have I1_prop xi : xi \in I1 -> (xi^*)%CF \notin I1.
  case/mapP => t; rewrite mem_filter /= => /andP [] i_lt_conj _ ->.
  apply: contraL i_lt_conj; rewrite -conjC_IirrE.
  case/mapP => s; rewrite mem_filter /= => /andP [] j_lt_conj _ /chi_inj ij.
  move: j_lt_conj; rewrite ij -{2}ij conjC_IirrK.
  by rewrite -leqNgt [(s <= t)%N]leq_eqVlt => ->; rewrite orbT.
have I1_I0_disjoint : [predI I0 & I1] =1 pred0.
  move => xi /=.
  case xiI0: (_ \in I0); rewrite (andTb, andFb) //.
  case xiI1: (_ \in I1) => //; move: xiI0 (I1_prop xi xiI1).
  by rewrite mem_filter /= => /andP [] /eqP ->; rewrite xiI1.
have I1_I2_disjoint : [predI I1 & I2] =1 pred0.
  move => xi /=; case xiI1: (_ \in I1); rewrite (andTb, andFb) //.
  case xiI2: (_ \in I2) => //.
  by case/mapP: xiI2 xiI1 => f /I1_prop fnI1 ->; rewrite (negPf fnI1).
have I0_I2_disjoint : [predI I0 & I2] =1 pred0.
  move => xi /=; case xiI0: (_ \in I0); rewrite (andTb, andFb) //.
  case xiI2: (_ \in I2) => //.
  case/mapP: xiI2 xiI0 => f fI1 ->; rewrite mem_filter /= => /andP [].
  rewrite cfConjCK => /eqP ffc.
  by move/I1_prop: (fI1); rewrite -ffc fI1.
have uniq_catI : uniq (I0 ++ I1 ++ I2).
  rewrite !cat_uniq I0_uniq I1_uniq I2_uniq has_cat negb_or /=.
  have has_disj (I J : seq 'CF(G)) : ([predI I & J] =1 pred0) -> ~~ has (mem I) J.
    move => disj; case h: (has _ _) => //.
    case/hasP: h => x; rewrite inE => xJ xI.
    by move: (disj x) => /=; rewrite xJ xI andbT.
  by rewrite !has_disj.
have irr_eq_catI : irr G =i I0 ++ I1 ++ I2.
  move => xi; rewrite !mem_cat; apply/idP/idP; last first.
    case/or3P; first by rewrite mem_filter => /andP [].
      by case/mapP => t _ ->; exact: irr_chi.
    by case/mapP => f; case/mapP => t _ -> ->; exact: cfConjC_irr.
  case/irrP => t ->.
  case: (ltngtP t (conjC_Iirr t)) => t_Iirr.
  - apply/orP; right; apply/orP; left; apply/mapP.
    by exists t => //; rewrite mem_filter /= t_Iirr andTb mem_enum.
  - apply/orP; right; apply/orP; right; apply/mapP.
    exists (('chi_t)^*)%CF; rewrite ?cfConjCK //.
    rewrite -conjC_IirrE; apply/mapP.
    by exists (conjC_Iirr t) => //; rewrite mem_filter /= conjC_IirrK t_Iirr mem_enum.
  by apply/orP; left; rewrite mem_filter irr_chi andbT /= -conjC_IirrE -(ord_inj t_Iirr).
have perm_eq_irr_catI : perm_eq (irr G) (I0 ++ I1 ++ I2) by exact: uniq_perm_eq.
have dZ a : d a \in 'Z[irr G].
  rewrite !add_vchar // ?opp_vchar -?chi0_1 ?irr_vchar //
       ?Dade_vchar ?(cfInd1_sub_lin_vchar _ (Schi a)) //.
  by rewrite nu_to ?seqInd_vcharW ?Schi.
have ->: '[d i, d j]_G = \sum_(xi <- irr G) '[d i, xi]_G * '[d j, xi]_G.
  symmetry; rewrite (cfdot_vchar_r _ (dZ j)) (big_nth 0) big_mkord.
  rewrite size_tuple; apply: eq_bigr => t _.
  by rewrite (tnth_nth 0).
rewrite (eq_big_perm _ perm_eq_irr_catI) !big_cat /=.
set sum0 := \sum_(i <- I0) _.
set sum1 := \sum_(i <- I1) _.
set sum2 := \sum_(i <- I2) _.
exists sum1.
  rewrite /sum1 big_seq_cond; apply: isIntC_sum => f /andP [].
  case/mapP => t _ -> _.
  by rewrite isIntC_mul ?cfdot_vchar_Int // ?irr_vchar.
have ->: sum0 = 0.
  rewrite /sum0 big1_seq // => f /andP [] _.
  rewrite mem_filter /= => /andP [] cf_f; case/irrP => t f_xi.
  move: cf_f; rewrite f_xi odd_eq_conj_irr1 // => /eqP ->.
  by rewrite d_ortho1 mul0r.
suff ->: sum2 = sum1 by rewrite add0r.
rewrite /sum2 /sum1 big_map big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP []; case/mapP => t _ -> _.
do 2 rewrite cfdotC -cfdot_conjC cfConjCK cfdotC mulrC.
by rewrite !d_conjC !isIntC_conj // cfdot_vchar_Int ?irr_vchar.
Qed.

Lemma pf79 i j : i != j -> 
  ('[beta i, nu j 'chi_(r j)] != 0) || ('[beta j, nu i 'chi_(r i)] != 0).
Proof.
move=> i_n_j.
have/eqP : '[beta i, nu j 'chi_(r j)] + '[beta j, nu i 'chi_(r i)] = 1 + '[d i, d j].
  rewrite !cfdotDl !cfdotDr !cfdotNl !cfdotNr.
  rewrite beta12_ortho // (dot_beta_1 (ddI i)) // nu_chi12_ortho //.
  rewrite !addrA !addr0 subrr add0r -!addrA; congr (_ + _); symmetry.
  rewrite cfdotC (dot_beta_1 (ddI j)) // cfnorm1.
  rewrite opprK !addrA conjC1 addNr add0r.
  rewrite cfdotC (@pf78a1 _ _ _ (ddI j) _ (nu j) (r j)) ?Schi //.
  rewrite (@pf78a1 _ _ _ (ddI i) _ (nu i) (r i)) ?Schi //.
  rewrite conjC0 oppr0 add0r addr0 cfdotC isIntC_conj //.
  rewrite cfdot_vchar_Int ?nu_to ?Dade_vchar
             ?(cfInd1_sub_lin_vchar _ (Schi j)) //.
  by rewrite seqInd_vcharW ?Schi.
apply: contraTT; rewrite negb_or !negbK.
move/andP => [] /eqP -> /eqP ->; rewrite addr0.
case: (dot_d12_even i j) => a; rewrite isIntCE; case/orP => /isNatCP [m].
  by move => -> ->; rewrite -natr_add -(natr_add _ 1) eq_sym -neq0N_neqC.
move/eqP; rewrite eqr_oppC => /eqP -> ->.
rewrite -!mulNrn -mulrn_addr mulNrn eq_sym subr_eq0 -(eqN_eqC 1).
have : odd 1 by [].
apply: contraL => /eqP ->.
by rewrite addnn odd_double.
Qed.

End PF79.

(*************************)
(* PF 7.10, PF 7.11 *)
Section PF7_10_11.

Hypothesis oddG : odd #|G|.

Variable k : nat.
(* L = K ><| H, Frobenius with kernel K *)
Variables (L K H : k.-tuple {group gT}).

Local Notation LL i := (tnth L i).
Local Notation KK i := (tnth K i).

Hypothesis k_ge2: (k >= 2)%N.
Hypothesis sLG : forall i : 'I_k, (LL i) \subset G.
(* Additional hypothesis *)
Hypothesis solvableL : forall i : 'I_k, solvable (LL i).

Hypothesis frobeniusL : 
  forall i : 'I_k, [Frobenius LL i = KK i ><| (tnth H i)].

Hypothesis normedTI_KL :
  forall i : 'I_k, normedTI (KK i)^# G (LL i).
Hypothesis card_coprime :
  forall i j : 'I_k, i != j -> coprime #|KK i| #|KK j|.

Let G0 := G :\: \bigcup_(i < k) class_support (KK i)^# G.

(* Connection with the Dade hypothesis *)

Let nKL i : KK i <| LL i.
Proof. by case/Frobenius_context: (frobeniusL i); case/sdprod_context. Qed.

Let sKL i : KK i \subset LL i. Proof. exact: normal_sub. Qed.

Let DadeH (a : gT) : {group gT} := 1%G.

Let ddA i : Dade_hypothesis G (LL i) DadeH (KK i)^#.
Proof.
apply/Dade_TI_P => //.
  rewrite subsetD1 !inE negb_and negbK eqxx orTb andbT.
  have sKG: (KK i) \subset G by rewrite (subset_trans (sKL i)) ?sLG.
  by rewrite (subset_trans _ sKG) // subsetDl.
case/Frobenius_context: (frobeniusL i) => _ Kn1 _ _ _.
apply: contra Kn1 => /eqP KD1.
by rewrite -(@setD1K _ 1%g (KK i)) ?in_group // KD1 setUC set0U.
Qed.

Local Notation tau i := (Dade (ddA i)).
Local Notation rho i := (rho_fun (ddA i)).
Local Notation Atau i := (Dade_support (ddA i)).

Let Dade_supp i : Atau i = class_support (KK i)^# G.
Proof.
rewrite /Dade_support class_supportEl.
apply: eq_bigr => x _.
by rewrite /Dade_support1 /DadeH mul1g class_supportEl big_set1.
Qed.

Let G0_def : G0 = G :\: \bigcup_(i < k) Atau i.
Proof. by congr (_ :\: _); apply: eq_bigr => i; rewrite Dade_supp. Qed.


(* Local definitions *)

Let h i := (#|KK i|%:R : algC).
Let e i := (#|LL i : KK i|%:R : algC).

Local Notation S i := (seqIndD (KK i) (LL i) (KK i) 1).

Let r (i : 'I_k) := odflt 0 [pick j | ('chi_j \in S i) && ('chi_j 1%g == e i)].

Let i1 := [arg min_(i < Ordinal k_ge2) #|KK i|].

(* Properties of the defined objects *)

Let i1_prop i : h i1 <= h i.
Proof. by rewrite -leq_leC /i1; case: arg_minP => // i1' _ ->. Qed.

(* This follows from Isaacs 6.34 *)
Let sSirrL i : {subset S i <= irr (LL i)}.
Proof.
move=> _ /seqIndC1P[t nz_t ->]; rewrite irr_induced_Frobenius_ker //.
exact: (Frobenius_cent1_ker (frobeniusL i)).
Qed.

Let chi_exists i : exists2 xi, xi \in S i & xi 1%g = e i.
Proof.
have/Frobenius_context [_ Kn1 _ _ _] := frobeniusL i.
by apply: exists_linInd; rewrite ?normal1 ?(solvableS (sKL i)) // proper1G.
Qed.

Let Schi i : 'chi_(r i) \in S i.
Proof.
rewrite /r; case: pickP => /=; first by move => j /andP [].
case: (chi_exists i) => xi xiS xi_e.
case/irrP: (sSirrL xiS) => t xi_t.
by move/(_ t); rewrite -xi_t xiS xi_e eqxx andTb.
Qed.

Let chi1 i : 'chi_(r i) 1%g = e i.
Proof.
rewrite /r; case: pickP => /=; first by move => j /andP [_] /eqP ->.
case: (chi_exists i) => xi xiS xi_e.
case/irrP: (sSirrL xiS) => t xi_t.
by move/(_ t); rewrite -xi_t xiS xi_e eqxx andTb.
Qed.

Let disjoint_Atau i j : i != j -> [disjoint (Atau i) & (Atau j)].
Proof.
move => i_n_j.
rewrite disjoint_subset; apply/subsetP => x; rewrite !inE.
rewrite !Dade_supp class_supportEr.
case/bigcupP => g gG; rewrite conjD1g !inE => /andP [] xn1 xKi.
apply: contraT; rewrite negbK class_supportEr.
case/bigcupP => y yG; rewrite conjD1g !inE => /andP [] _ xKj.
move: (order_dvdG xKi) (order_dvdG xKj); rewrite !cardJg => x_i x_j.
have: #[x] == 1%N.
  rewrite -dvdn1; move: (card_coprime i_n_j); rewrite /coprime => /eqP <-.
  by rewrite dvdn_gcd x_i x_j.
by rewrite order_eq1 (negPf xn1).
Qed.


(*************************)
(* Coherence hypotheses  *)
(*************************)

(* This follows from PF 6.8 *)
Variable nu : forall i, {additive 'CF(LL i) -> 'CF(G)}.

(*
Hypothesis coherent_hyp : 
  forall i : 'I_k, my_coherent 'LL_i G (S i) ('KK_i)^# (cinduced G 'LL_i) (nu i).
*)

Hypothesis S_non_trivial : forall i, 
  exists2 theta, theta \in 'Z[S i, (KK i)^#] & theta != 0.
Hypothesis nu_isom : forall i, {in 'Z[S i] &, isometry (nu i)}.
Hypothesis nu_to : forall i, {in 'Z[S i], forall phi, (nu i) phi \in 'Z[irr G]}.
Hypothesis nu_ind : forall i, {in 'Z[S i, (KK i)^#], nu i =1 'Ind[G, LL i]}.

Let nu_tau i : {in 'Z[S i, (KK i)^#], nu i =1 Dade (ddA i)}.
Proof.
move => f fZ /=.
rewrite nu_ind // Dade_Ind ?vchar_on //.
by apply: (vchar_on fZ).
Qed.


(************************************)

Let beta i := ((tau i) ('Ind[LL i, KK i] 1 - 'chi_(r i))).
Let calB := [pred i : 'I_k | ('[beta i, (nu i1) ('chi_(r i1))]_G == 0) && (i != i1)].

Local Notation e1 := (e i1).
Local Notation h1 := (h i1).
Local Notation nu1 := (nu i1).


Let en0 i : e i != 0. Proof. exact: neq0GiC. Qed.
Let hn0 i : h i != 0. Proof. exact: neq0GC. Qed.
Let eh i : e i * h i = #|LL i|%:R.
Proof. by rewrite -(LaGrange (sKL i)) natr_mul mulrC. Qed.

Let e_cardH i : e i = #|tnth H i|%:R.
Proof.
apply/eqP; rewrite -eqN_eqC.
have/Frobenius_context [KH_L _ _ _ _] := frobeniusL i.
have := LaGrange (sKL i); move/sdprod_card: KH_L <-.
move/eqP; rewrite eqn_mul2l.
case cK: (_ == 0)%N; last by rewrite orFb.
by have := cardG_gt0 (KK i); move/eqP: cK ->.
Qed.

Let e_gt1 i : 1 < e i.
Proof.
rewrite e_cardH -(ltn_ltC 1).
case: (ltngtP 1 #|tnth H i|) => //.
  by apply: contraTT; rewrite -leqNgt cardG_gt0.
have/Frobenius_context [_ _ Hn1 _ _] := frobeniusL i.
by move/esym/eqP; rewrite -trivg_card1 (negPf Hn1).
Qed.

Let h_gt1 i : 1 < h i.
Proof.
rewrite -(ltn_ltC 1).
case: (ltngtP 1 #|KK i|) => //.
  by apply: contraTT; rewrite -leqNgt cardG_gt0.
have/Frobenius_context [_ Kn1 _ _ _] := frobeniusL i.
by move/esym/eqP; rewrite -trivg_card1 (negPf Kn1).
Qed.

Let cardA i : #|(KK i)^#|%:R = h i - 1.
Proof.
have := cardsD1 1%g (KK i); rewrite in_group => /eqP.
by rewrite eqN_eqC natr_add addrC -subr_eq => /eqP ->.
Qed.

Let eh_ineq i : e i <= (h i - 1) / 2%:R.
Proof.
have two_n0: 2%:R != (0 : algC) by rewrite -neq0N_neqC.
rewrite -[e i]mulr1 -{1}[1](mulfV two_n0) mulrA leC_mul2r ?posC_inv ?posC_nat //.
rewrite -(leC_add2r 1) subrK e_cardH /h.
rewrite -natr_mul -[_ + 1%:R]natr_add -leq_leC.
have := Frobenius_dvd_ker1 (frobeniusL i).
set a := #|_|; set b := #|_|.
have/Frobenius_context [KH_L Kn1 _ _ /proper_sub sHL]:= (frobeniusL i).
have b_gt0: (0 < b)%N by rewrite /b cardG_gt0.
have b_gt1: (1 < b)%N.
  case: (ltngtP 1 b) => //; first by rewrite ltnNge b_gt0.
  by move/esym/eqP; rewrite /b -trivg_card1 (negPf Kn1).
have b_eq: exists m, b = m.+2 by exists (b - 2)%N; rewrite -addn2 (subnK b_gt1).
case/dvdnP => q; case: q => [| q].
  by case: b_eq => m ->; rewrite mul0n.
case: q => [| q]; last first.
  case: b_eq => m ->.
  rewrite -{2}(prednK (ltn0Sn (m.+1))) => ->.
  rewrite -[(_ * _).+1]addn1 leq_add2r -[q.+2]addn2 muln_addl mulnC.
  by rewrite -{1}[(_ * _)%N]add0n leq_add2r leq0n.
rewrite mul1n => b1_a.
have: ~~ odd (b.-1).
  by rewrite -subn1 (odd_sub b_gt0) /b (oddSg (sKL i)) ?(oddSg (sLG i)).
have: odd a by rewrite /a (oddSg sHL) ?(oddSg (sLG i)).
by rewrite -b1_a => ->.
Qed.

Let h1_lt_others i : i != i1 -> h1 + 2%:R <= h i.
Proof.
move => i_n_1; move: (i1_prop i).
rewrite -natr_add -!leq_leC.
set a := #|_|; set b := #|_|; move => a_le_b.
case: (ltngtP (a + 1%N) b).
- by rewrite -[2]addn1 addnA !addn1.
- rewrite -addn1 leq_add2r => b_le_a.
  have ab: a = b by apply: anti_leq; rewrite a_le_b b_le_a.
  have := card_coprime i_n_1.
  rewrite -/a -/b ab /coprime gcdnn => /eqP b1.
  by have := h_gt1 i; rewrite -(ltn_ltC 1) -/b b1 ltnn.
move => a1_b.
have: ~~ odd (a + 1) by rewrite odd_add (oddSg (sKL i1)) ?(oddSg (sLG i1)).
have: odd b by rewrite (oddSg (sKL i)) ?(oddSg (sLG i)).
by rewrite a1_b => ->.
Qed.

Let normS i f : f \in S i -> '[f]_(LL i) = 1.
Proof. by move/sSirrL; case/irrP => t ->; rewrite cfdot_irr eqxx. Qed.

Let norm_nuS i f : f \in S i -> '[(nu i) f, (nu i) f]_G = 1.
Proof. by move => fS; rewrite nu_isom ?seqInd_vcharW // normS. Qed.

Let nu_ij_ortho i j f g : i != j -> f \in S i -> g \in S j ->
  '[(nu i) f, (nu j) g]_G = 0.
Proof.
move => i_n_j fS gS.
pose X a u := [:: (nu a) u; (nu a) ((u^*)%CF)].
have X_ortho a u : u \in S a -> orthonormal (X a u).
  move => uS; case/irrP: (sSirrL uS) => q xi_q.
  apply/orthonormal2P; rewrite ?memc_Zirr ?nu_to ?seqInd_vcharW ?cfAut_seqInd //.
  split; rewrite nu_isom ?seqInd_vcharW ?cfAut_seqInd // xi_q ?cfnorm_irr //.
    by rewrite -xi_q (seqInd_conjC_ortho (nKL a) _ _ uS) ?(oddSg (sLG a)).
  by rewrite -conjC_IirrE cfnorm_irr.
have sXZirr a u : u \in S a -> {subset X a u <= 'Z[irr G]}.
  by move => uS ff; rewrite 2!inE; case/orP => /eqP ->;
    rewrite nu_to ?seqInd_vcharW ?cfAut_seqInd.
have/(_ 1 1) := vchar_pairs_orthonormal (conj (sXZirr i f fS) (sXZirr j g gS)).
rewrite !X_ortho // nonzero1r (isIntC_Real (isIntC_nat 1)) /=.
rewrite !scale1r -!raddf_sub.
rewrite [(nu i) (_ - _)]nu_tau ?[(nu j) (_ - _)]nu_tau ?seqInd_sub_Aut_vchar //.
rewrite !Dade1 eqxx.
set prod := '[_, _].
have ->: prod == 0.
  rewrite /prod (@cfdot_complement _ G (Atau i)) //.
    by rewrite Dade_cfunS.
  set mu := _ - _.
  have: (tau j) mu \in 'CF(G, Atau j) by rewrite Dade_cfunS.
  rewrite !cfun_onE => sA.
  apply: (subset_trans sA).
  by rewrite subsetD disjoint_sym (disjoint_Atau i_n_j) Dade_support_sub.
move => /(_ isT isT isT) /orthonormalP [] => uniq_abcd.
move => /(_ (nu i f) (nu j g)); rewrite !inE !eqxx !orbT /=.
move => /(_ isT isT) ->; move: uniq_abcd => /=.
by rewrite !inE !negb_or => /andP [] /and3P [] => _ /negPf ->.
Qed.


(*************************************)

Let ineq1 : 1 - e1 / h1 - (h1 - 1) / (e1 * h1) - 
  \sum_(i \in calB) (h i - 1) / (e i * h i) <= (#|G0|%:R - 1) / #|G|%:R.
Proof.
set lhs := 1 - _ - _ - _.
set rhs := _ / _.
have nu_chi1_Z: nu1 ('chi_(r i1)) \in 'Z[irr G].
  by rewrite nu_to ?seqInd_vcharW ?Schi.
case: (vchar_norm1P nu_chi1_Z (norm_nuS (Schi i1))) => eps [t] nu_chi1_irr.
have: #|G|%:R ^-1 * (#|G0|%:R - \sum_(g \in G0) `|'chi_t g| ^+ 2) <= rhs.
  rewrite mulrC leC_pmul2r ?sposC_inv ?sposGC // leC_add2l leC_opp G0_def.
  rewrite (big_setD1 1%g) /=; last first.
    rewrite inE in_group andbT; apply: contraT; rewrite negbK.
    case/bigcupP => i _; rewrite Dade_supp class_supportEr.
    by case/bigcupP => x _; rewrite conjD1g !inE eqxx andFb.
  rewrite -[1]addr0 leC_add //; last first.
    by apply: posC_sum => g _; rewrite -normC_exp posC_norm.
  have rZ: isIntC ('chi_t 1%g) by rewrite isIntCE isNatC_irr1.
  by rewrite int_normCK // isIntC_expr2_ge1 ?irr1_neq0.
pose A := [tuple of (map (fun X : {group gT} => X^#) K)].
pose HH := [tuple of (map (fun X : {group gT} => DadeH) K)].
have ddI i : Dade_hypothesis G (LL i) (tnth HH i) (tnth A i).
  by rewrite !tnth_map.
have D_supp i: Dade_support (ddI i) = Atau i.
  rewrite /Dade_support {1}tnth_map; apply: eq_bigr => g _.
  by rewrite /Dade_support1 tnth_map.
have Dade_disj i j : i != j -> [disjoint Dade_support (ddI i) & Dade_support (ddI j)].
  by move => i_n_j; rewrite !D_supp (disjoint_Atau i_n_j).
have := @pf75 _ A L HH ddI Dade_disj t.
set G0_0 := _ :\: _.
have ->: G0_0 = G0.
  by rewrite G0_def /G0_0; congr (_ :\: _); apply: eq_bigr => i _.
rewrite -[_ * _]opprK -mulrN oppr_sub -leC_opp oppr0 oppr_add opprK leC_sub.
rewrite /rhs => {rhs}; set rhs := \sum_(i < k) _.
suff: lhs <= rhs.
  by move => ineq1 ineq2; move: (leC_trans ineq1 ineq2); exact: leC_trans.
rewrite /rhs (bigD1 i1) //= (bigID calB) /=.
have rho_eq i : rho_fun (ddI i) =1 rho i.
  by move => f; apply/cfunP => x; rewrite !cfunElock !tnth_map.
rewrite /lhs leC_add //.
  rewrite leC_add //; last by rewrite leC_opp tnth_map eh cardA leC_refl.
  set X := '[_]_ _.
  have {X}->: X = '[rho i1 (nu1 'chi_(r i1))].
    rewrite /X nu_chi1_irr linearZ cfnormZ int_normCK ?isIntC_sign //=.
    by rewrite sqrr_sign mul1r rho_eq.
  by rewrite pf78b1 // ?chi1 ?eh_ineq.
rewrite -[- _]addr0 leC_add //.
  have ->: \sum_(i \in calB) (h i - 1) / (e i * h i) =
    \sum_(i < k | [&& i != i1, '[beta i, nu1 ('chi_(r i1))]_G == 0 & i != i1]) (h i - 1) / (e i * h i).
    apply: eq_bigl => i; rewrite /calB !inE; apply/idP/idP.
      by move/andP => [] -> ->.
    by move/andP => [] -> ->.
  rewrite -leC_sub opprK -big_split posC_sum //= => i _.
  rewrite -[0]addr0 -addrA leC_add ?cfnorm_posC //.
  by rewrite addrC tnth_map cardA eh subrr leC_refl.
apply: posC_sum => i /andP [] i_n1; rewrite i_n1 negb_and orbF => beta_chi_n0.
rewrite rho_eq tnth_map.
rewrite (@pf78c2 (KK i) (LL i) DadeH _ _ (nu i) (r i)) // ?irr_chi ?chi1 //; last first.
  move => f fS; have := nu_ij_ortho i_n1 fS (Schi i1).
  rewrite nu_chi1_irr cfdotZr => /eqP; rewrite mulf_eq0; case/orP.
    by rewrite conjC_eq0 signr_eq0.
  by move/eqP.
rewrite -leC_sub -{2}[_ / _]mulr1 -mulr_subr subr0 !posC_mul ?posC_inv ?posC_nat //.
rewrite leC_sub isIntC_expr2_ge1 //.
  by rewrite cfdot_vchar_Int ?irr_vchar ?Dade_vchar ?(cfInd1_sub_lin_vchar _ (Schi i)) ?chi1 //.
move: beta_chi_n0; rewrite nu_chi1_irr cfdotZr mulf_eq0 negb_or.
by move/andP => [].
Qed.


(**************************************)

Let ineq2 : \sum_(i \in calB) (h i - 1) / (e i) <= e1 - 1.
Proof.
have := pf78a2 (nKL i1) (Schi i1) (chi1 i1) (S_non_trivial i1)
           (@nu_isom i1) (@nu_to i1) (@nu_tau i1).
rewrite -/e1.
move => [a] [Gamma] [] _ Gamma1 Gamma_nu beta_eq.
have fe_nat i f: f \in S i -> exists m, (f 1%g / e i) = m%:R.
  move => fS; apply/isNatCP; case/seqIndP: fS => t _ ->.
  by rewrite cfInd1 -/(e i) // mulrAC mulfV // mul1r isNatC_irr1.
pose cx i := '[beta i1, (nu i) ('chi_(r i))]_G.
pose X : 'CF(G) := \sum_(i < k | i != i1) cx i *: 
  \sum_(f <- S i) f 1%g / e i *: (nu i) f.
have X_ortho: '[Gamma - X, X]_G = 0.
  suff ortho i f: i != i1 -> f \in S i -> '[Gamma - X, (nu i) f]_G = 0.
    rewrite {2}/X cfdot_sumr big1 // => i i_n_1.
    rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 // => f /andP [_ fS] /=.
    by rewrite cfdotZr ortho // mulr0.
  move => i_n_1 fS.
  rewrite cfdot_subl.
  have ->: '[X, (nu i) f]_G = f 1%g / e i * cx i.
    rewrite cfdot_suml (bigD1 i) //= cfdotZl cfdot_suml.
    rewrite (bigD1_seq f) ?seqInd_uniq //= big1_seq; last first.
      move=> g /andP[g_n_f gS]; rewrite cfdotZl.
      by rewrite nu_isom ?seqInd_vcharW // (seqInd_ortho (nKL i) gS) // mulr0.
    rewrite addr0 cfdotZl norm_nuS // mulr1 mulrC.
    rewrite big1 ?addr0 // => j /andP [_ j_n_i].
    rewrite cfdotZl cfdot_suml big1_seq ?mulr0 // => g /andP [_ gS].
    by rewrite cfdotZl nu_ij_ortho ?mulr0.
  have ->: '[Gamma, (nu i) f]_G = '[beta i1, (nu i) f]_G.
    rewrite /beta beta_eq !cfdotDl cfdotNl cfdotZl.
    rewrite nu_ij_ortho ?Schi //; last by rewrite eq_sym.
    rewrite ['[1, _]_G]cfdotC.
    rewrite (@pf78a1 (KK i) (LL i) DadeH _ _ (nu i) (r i)) ?chi1 //.
    rewrite conjC0 addr0 subr0 addrC; apply/esym.
    rewrite cfdot_suml big1_seq ?mulr0 ?add0r // => g /andP [_ gS].
    by rewrite cfdotZl nu_ij_ortho ?mulr0 // eq_sym.
  have [m fe_m] := fe_nat i f fS.
  rewrite /cx fe_m -conjC_nat -cfdotZr -cfdotNr -cfdotDr.
  rewrite scaler_nat -raddfMn -raddf_sub nu_tau //; last first.
    by rewrite -scaler_nat -fe_m seqInd_sub_lin_vchar ?chi1 ?Schi.
  rewrite (@cfdot_complement _ G (Atau i1)) //.
    by rewrite Dade_cfunS.
  have: (tau i) (f - 'chi_(r i) *+ m) \in 'CF(G, Atau i).
    by rewrite Dade_cfunS.
  rewrite !cfun_onE => sA; apply: (subset_trans sA).
  by rewrite subsetD disjoint_Atau // Dade_support_sub.
have norm_X : '[X]_G <= e1 - 1.
  have := pf78b2 (nKL i1) (Schi i1) (chi1 i1) (S_non_trivial i1)
             (@nu_isom i1) (@nu_to i1) (@nu_tau i1) (eh_ineq i1) Gamma1 Gamma_nu beta_eq.
  rewrite -/e1; apply: leC_trans.
  have ->: Gamma = (Gamma - X) + X by rewrite subrK.
  by rewrite cfnormD X_ortho conjC0 !addr0 -leC_sub addrK cfnorm_posC.
apply: leC_trans norm_X.
have x_Z i : isIntC (cx i).
  rewrite /cx cfdot_vchar_Int ?nu_to ?seqInd_vcharW ?Dade_vchar ?Schi //.
  by rewrite (cfInd1_sub_lin_vchar _ (Schi _)) ?chi1.
have ->: '[X]_G = \sum_(i < k | i != i1) (cx i) ^+ 2 *
                       \sum_(f <- S i) (f 1%g / e i) ^+ 2 / '[f]_(LL i).
  rewrite {2}/X raddf_sum; apply: eq_bigr => i i_n_1 /=.
  rewrite cfdotZr /X cfdot_suml (bigD1 i) //= addrC.
  rewrite big1 ?add0r; last first.
    move => j /andP [_ j_n_i]; rewrite cfdotZl cfdot_suml big1_seq ?mulr0 //=.
    move => f fS; rewrite cfdot_sumr big1_seq //=.
    by move => g gS; rewrite cfdotZl cfdotZr nu_ij_ortho ?mulr0.
  rewrite cfdotZl isIntC_conj // mulrA -expr2; congr (_ * _).
  rewrite cfdot_sumr big_seq [in X in _ = X]big_seq /=.
  apply: eq_bigr => f fS; rewrite cfdot_suml.
  have [m fe_m] := fe_nat i f fS.
  rewrite (bigD1_seq f) ?seqInd_uniq //= big1_seq.
    rewrite addr0 cfnormZ fe_m normC_nat.
    by rewrite norm_nuS ?normS // invr1.
  move => g /andP [g_n_f] gS; rewrite cfdotZl cfdotZr.
  by rewrite nu_isom ?seqInd_vcharW // (seqInd_ortho (nKL i) gS) // !mulr0.
rewrite -[\sum_(i \in calB) _]addr0 [in X in _ <= X](bigID calB) /=.
rewrite leC_add //; last first.
  apply: posC_sum => i _; rewrite -int_normCK // -normC_exp posC_mul ?posC_norm //.
  rewrite big_seq posC_sum // => f fS; case: (fe_nat i f fS) => m ->.
  by rewrite posC_mul ?posC_inv ?cfnorm_posC // expr2 posC_mul ?posC_nat.
have ->: \sum_(i \in calB) (h i - 1) / e i =
  \sum_(i < k | [&& i != i1, '[beta i, nu1 ('chi_(r i1))]_G == 0 & i != i1]) (h i - 1) / e i.
    by apply: eq_bigl => i; rewrite /calB !inE; apply/idP/idP; move/andP => [] -> ->.
rewrite -leC_sub -sumr_sub posC_sum // => i /and3P [] i_n_1 beta_nu0 _.
have ->: \sum_(f <- S i) (f 1%g / e i) ^+ 2 / '[f]
          = (\sum_(f <- S i) f 1%g ^+ 2 / '[f]) / (e i) ^+ 2.
  rewrite -expr_inv big_distrl; apply: eq_bigr => phi _ /=.
  by rewrite exprn_mull mulrAC.
rewrite sum_seqIndC1_square // -/(e i) -/(h i).
rewrite -expr_inv (mulrCA (e i * _)) -(mulrA (e i)) mulKf ?neq0GiC //.
have cx_n0: cx i != 0.
  pose HH := [tuple of (map (fun X : {group gT} => DadeH) K)].
  have ddI x : Dade_hypothesis G (LL x) (tnth HH x) (KK x)^#.
    by rewrite !tnth_map.
  have D_supp x: Dade_support (ddI x) = Atau x.
    by rewrite /Dade_support; apply: eq_bigr => g _; rewrite /Dade_support1 tnth_map.
  have Dade_disj x y : x != y -> [disjoint Dade_support (ddI x) & Dade_support (ddI y)].
    by move => x_n_y; rewrite !D_supp (disjoint_Atau x_n_y).
  have tau_eq x : Dade (ddI x) =1 tau x.
    move => y; apply/cfunP => z.
    by rewrite !cfunElock /Dade_support1 tnth_map.
  have nu_tauI x : {in 'Z[S x, (KK x)^#], nu x =1 Dade (ddI x)}.
    by move => f fZ /=; rewrite nu_tau // tau_eq.
  have := pf79 oddG Dade_disj nKL S_non_trivial nu_isom nu_to nu_tauI Schi chi1 i_n_1.
  by rewrite !tau_eq beta_nu0 orFb.
rewrite leC_sub -{1}[_ / _]mul1r leC_mul2r ?isIntC_expr2_ge1 //.
rewrite posC_mul ?posC_inv /e ?posC_nat // leC_sub.
by rewrite /h -(leq_leC 1) cardG_gt0.
Qed.

Let ineq3 : \sum_(i \in calB) (h i - 1) / (e i * h i) <= (e1 - 1) / (h1 + 2%:R).
Proof.
suff ineq: \sum_(i \in calB) (h i - 1) / (e i * h i) <= 
  \sum_(i \in calB) (h i - 1) / e i / (h1 + 2%:R).
  apply: (leC_trans ineq).
  by rewrite mulr_suml leC_mul2r ?posC_inv -?natr_add -?(leq_leC 0) ?addn2.
rewrite -leC_sub -sumr_sub posC_sum // => i.
rewrite /calB !inE => /andP [_] i_n_1.
rewrite invf_mul mulrA leC_sub leC_mul2l ?posC_mul ?posC_inv -?cardA ?posC_nat //.
rewrite -[(h i)^-1]mul1r -[(_ + _)^-1]mulr1 -{3}(mulfV (hn0 i)) mulrA.
rewrite leC_mul2r ?posC_inv ?posC_nat //.
have h2_n0 : h1 + 2%:R != 0 by rewrite -natr_add -neq0N_neqC addn2.
rewrite -{1}(mulVf h2_n0) leC_mul2l ?posC_inv -?natr_add ?posC_nat //.
by rewrite natr_add h1_lt_others.
Qed.


Lemma pf7_10 : exists i,
  let ei := e i in let hi := h i in
  (ei - 1) * ((hi - 2%:R * ei - 1) / (ei * hi) + 2%:R / (hi * (hi + 2%:R)))
     <= (#|G0|%:R - 1) / #|G|%:R.
Proof.
exists i1.
apply: leC_trans ineq1.
rewrite mulr_addr mulr_subl mulrCA mul1r {1}invf_mul !mulrA mulfK //.
rewrite 2!mulr_subl mulr_natl mulr2n mulfV // mulr_addl oppr_add.
rewrite [_ - _ - 1]addrAC mulr_subl oppr_add -!addrA !leC_add2l.
rewrite addrA addrC -addrA leC_add2l opprK -[_ + _]opprK leC_opp.
rewrite !oppr_add !opprK mulr_addl !invf_mul mulrA mulfV // addrC oppr_add.
rewrite 2!addrA addrK -mulr_subl -mulrA -mulr_subr.
have h1_2: h1 + 2%:R != 0 by rewrite -natr_add -neq0N_neqC addn2.
rewrite [_ * (_ / _)]mulrC -{1}[h1^-1]mulr1 -{3}(mulVf h1_2) mulrA.
by rewrite -mulr_subr -addrA subrr addr0 mulrAC mulVf // mul1r ineq3.
Qed.


(***************************************)

(* PF 7.11 *)

Theorem pf7_11 : G0 != 1%G.
Proof.
case: pf7_10 => i; apply: contraL => /eqP ->.
rewrite cards1 subrr mul0r ltC_geF //.
rewrite sposC_mul -?ltC_sub //.
set X := _ / _; set Y := _ / _.
have: X <= Y + X.
  rewrite -leC_sub addrK /Y eh posC_mul ?posC_inv ?posC_nat //.
  have two_n0: 2%:R != (0 : algC) by rewrite -neq0N_neqC.
  rewrite addrAC leC_sub -[_ - _]mul1r -{2}(mulfV two_n0) -mulrA.
  by rewrite leC_mul2l -?(leq_leC 0) // mulrC.
apply: ltC_leC_trans.
rewrite sposC_mul ?sposC_inv -?(ltn_ltC 0) //.
by rewrite sposC_mul -?natr_add -?(ltn_ltC 0) ?cardG_gt0 // addn2.
Qed.

End PF7_10_11.

End Seven.

