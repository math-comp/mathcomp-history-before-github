(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator nilpotent.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import frobenius inertia vcharacter. 
Require Import PFsection1 PFsection2 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 6:                                    *)
(* Some Coherence Theorems                                                    *)
(* Defined here:                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.


(* Additional results about sequences *)
Section MoreSeq.

Variable (T : eqType).
Implicit Type s : seq T.

Lemma rem_cons_size s x : x \in s ->
  size (x :: rem x s) = size s.
Proof.
by move => xs; apply: perm_eq_size; rewrite perm_eq_sym; exact: perm_to_rem.
Qed.


(* Analog of nthP for tuples *)
Lemma tnthP m (t : m.-tuple T) x : reflect (exists j, x = tnth t j) (x \in t).
Proof.
apply: (iffP idP) => [/nthP | [] j ->]; last first.
  by apply/(@nthP T t _ x); exists j; rewrite ?(size_tuple, ltn_ord) -?tnth_nth.
move/(_ x) => [] j j_lt_m <-; rewrite size_tuple in j_lt_m.
by exists (Ordinal j_lt_m); rewrite (tnth_nth x).
Qed.

End MoreSeq.



(* Additional results for big operators *)
Section MoreBig.

Variable T : eqType.
Variable R : Type.
Variable idx : R.
Variable op : Monoid.law idx.

Lemma filter_pred1_uniq (s : seq T) x :
  uniq s -> x \in s -> filter (pred1 x) s = [:: x].
Proof.
elim: s => //= h t IHt /andP [] hnt uniq_t.
rewrite in_cons; case/orP => [/eqP ->|].
  rewrite eqxx; congr (_ :: _); apply/eqP; apply: contraNT hnt.
  rewrite -has_filter; case/hasP => y /=.
  by case yh: (_ == _); [ move/eqP: yh -> | ].
move => xt; case hx: (_ == _); last by exact: IHt.
by move/eqP: hx xt hnt -> => ->.
Qed.

Lemma big_pred1_uniq (s : seq T) x F : 
  uniq s -> x \in s -> \big[op/idx]_(i <- s | i == x) F i = F x.
Proof.
move => uniq_s xs.
by rewrite -big_filter filter_pred1_uniq // big_cons big_nil Monoid.mulm1.
Qed.

End MoreBig.


(* Additional propertries of the inner product *)
Section MoreInnerProd.

Variable gT : finGroupType.
Variable G : {group gT}.

Lemma cfnormE (S : {set gT}) (f : 'CF(G)) : 
  f \in 'CF(G, S) -> '[f] = #|G|%:R^-1 * (\sum_(x \in S) `|f x| ^+ 2).
Proof.
move => fGS; rewrite (cfdotEl _ fGS); congr (_ * _).
by apply: eq_bigr => x _; rewrite normCK.
Qed.

Lemma pairwise_orthogonal_filter (S : seq 'CF(G)) p : 
  pairwise_orthogonal S -> pairwise_orthogonal (filter p S).
Proof.
move => orthoS.
apply: (sub_pairwise_orthogonal _ _ orthoS).
  exact: mem_subseq (filter_subseq p S).
apply: filter_uniq; case/pairwise_orthogonalP: orthoS.
by rewrite cons_uniq => /andP [].
Qed.

Lemma orthonormal2P (a b : 'CF(G)) :
  reflect [/\ '[a, b] = 0, '[a] = 1 & '[b] = 1] (orthonormal [:: a; b]).
Proof.
apply: (iffP idP).
  move/orthonormalP => [] /=; rewrite inE => /andP [a_n_b _] ortho; split.
  - by move/(_ a b): ortho; rewrite !inE !eqxx orTb orbT (negPf a_n_b); apply.
  - by move/(_ a a): ortho; rewrite !inE eqxx orTb; apply.
  by move/(_ b b): ortho; rewrite !inE eqxx orbT; apply.
move => [] ab0 a1 b1; apply/orthonormalP.
have a_n_b: a != b.
  by move/eqP: ab0; apply: contraL => /eqP ->; rewrite b1 nonzero1r.
split => /=.
  by rewrite inE a_n_b.
by move => x y; rewrite !inE; case/orP => /eqP ->; case/orP => /eqP ->;
  rewrite ?eqxx ?(negPf a_n_b) // cfdotC eq_sym (negPf a_n_b) ab0 conjC0.
Qed.

End MoreInnerProd.



(* Additional results about characters *)
Section MoreChar.

Variable gT : finGroupType.
Variable G L K : {group gT}.

Lemma cfnorm_Ind1 : K <| L -> '['Ind[L, K] 1] = #|L : K|%:R.
Proof.
move => nKL; have sKL := normal_sub nKL.
rewrite (cfnormE (cfInd_normal _ nKL)).
apply: (mulfI (neq0GC L)); rewrite mulrA mulfV ?neq0GC // mul1r.
rewrite -(LaGrange sKL) -sum1_card natr_mul natr_sum -!mulr_suml.
apply: eq_bigr => y yK.
by rewrite cfInd_cfun1 // cfunE cfuniE // yK mulr1 normC_nat expr2 mul1r.
Qed.

(* Each solvable (non-trivial) group has a non-trivial linear character *)
Lemma lin_char_solvable : G != 1%G -> solvable G -> 
  exists2 i, lin_char 'chi[G]_i & 'chi[G]_i != 1.
Proof.
move => Gn1 solvG.
pose n := #|G : G^`(1)%g|.
have n_gt1: (1 < n)%N.
  by rewrite indexg_gt1 proper_subn // (sol_der1_proper solvG).
have := cardD1 (0 : Iirr G) [pred i | lin_char 'chi_i].
rewrite !inE chi0_1 cfun1_lin_char card_lin_irr -/n.
rewrite  -(subnK n_gt1) add1n addn2 => /eqP; rewrite eqSS eq_sym => /eqP eq.
have := ltn0Sn (n - 2); rewrite -eq.
case/card_gt0P => i; rewrite !inE => /andP [i_n0 linear_i].
by exists i => //; rewrite -chi0_1; apply: contra i_n0 => /eqP/chi_inj ->.
Qed.

Lemma conjg_Iirr0 x : conjg_Iirr (0 : Iirr K) x = 0.
Proof. by apply: chi_inj; rewrite conjg_IirrE chi0_1 cfConjg_cfun1. Qed.

(* Isaacs 6.34(a1) *)
Lemma inertia_Frobenius_ker i : K <| G -> i != 0 ->
  {in K^#, forall x, 'C_G[x] \subset K} -> 'I_G['chi[K]_i] = K.
Proof.
move => nKG i_n0 centGK; apply/eqP.
move/andP: (nKG) => [sKG sGNK].
rewrite eqEsubset sub_inertia // andbT.
apply/subsetP => x; rewrite !inE => /andP [/andP []] xG _ x_stab_i.
have xNK : x \in 'N(K) by exact: (subsetP sGNK).
pose ito_f (i : Iirr K) g := if g \in G then conjg_Iirr i g else i.
have action_ito: is_action G ito_f.
  split; last first.
    move => r g h gG hG; rewrite /ito_f in_group // hG gG.
    by apply: chi_inj; rewrite !conjg_IirrE cfConjgMnorm ?(subsetP sGNK).
  move => g t r; rewrite /ito_f; case gG: (g \in G); last by [].
  move => conj_eq; apply: chi_inj.
  rewrite -['chi_t]cfConjg1 -(mulgV g) cfConjgMnorm ?in_group ?(subsetP sGNK) //.
  rewrite -conjg_IirrE conj_eq conjg_IirrE -cfConjgMnorm ?(in_group, subsetP sGNK) //.
  by rewrite mulgV cfConjg1.
pose ito := Action action_ito.
pose cto := ('Js \ (subsetT G))%act.
have acts_Js : [acts G, on classes K | 'Js].
  apply/actsP => g gG C /=; apply/imsetP/imsetP => [] [] h hK.
    rewrite -[h ^: K]conjsg1 -(mulVg g) conjsgM => /conjsg_inj.
    rewrite -class_rcoset norm_rlcoset ?in_group ?(subsetP sGNK) //.
    rewrite class_lcoset => ->; exists (h ^ (g^-1)) => //.
    by rewrite memJ_norm // in_group (subsetP sGNK).
  move ->; exists (h ^ g); first by rewrite memJ_norm ?(subsetP sGNK).
  by rewrite -class_rcoset norm_rlcoset ?(subsetP sGNK) // class_lcoset.
have acts_cto : [acts G, on classes K | cto].
  by rewrite astabs_ract subsetI subxx.
have ito_cto_id r k y : k \in K -> y \in cto (k ^: K) x -> 
  'chi_r k = 'chi_(ito r x) y.
  move => xK; case/imsetP => z; case/imsetP => h hK -> ->.
  rewrite /= /ito_f xG conjg_IirrE cfConjgE ?(subsetP sGNK) //.
  by rewrite -conjgM mulgV conjg1 cfunJ.
have := @card_afix_irr_classes _ _ G K ito cto _ xG acts_cto ito_cto_id.
set n := #|_|; set m := #|_| => nm.
have: (1 < m)%N.
  rewrite -nm /n (cardsD1 (0 : Iirr K)) inE sub1set inE /= /ito_f xG.
  rewrite conjg_Iirr0 // eqxx -addn1 leq_add2l.
  apply/card_gt0P; exists i; rewrite !inE sub1set inE i_n0 andTb /= /ito_f xG.
  by apply/eqP/chi_inj; rewrite conjg_IirrE (eqP x_stab_i).
case xnK: (x \in K) => //.
suff ->: m = 1%N by rewrite ltnn.
rewrite /m; apply/eqP/cards1P; exists 1%g; apply/eqP.
rewrite eqEsubset sub1set; apply/andP; split; last first.
  by rewrite !inE classes1 andTb sub1set inE /= conjs1g.
apply/subsetP => C; rewrite !inE sub1set inE /= => /andP [/imsetP [h hK ->]].
rewrite eqEsubset => /andP [/subsetP/( _ (h ^ x))].
rewrite -class_rcoset norm_rlcoset // class_lcoset class_refl => /(_ isT).
move/imsetP => [t] tK; rewrite -[h ^ x]conjg1 -(mulVg t) conjgM => /conjg_inj.
rewrite -conjgM => /conjg_fixP/commgP/commute_sym/cent1P => xtC _.
case: (boolP (h \in K^#)); rewrite !inE hK andbT ?negbK; last first.
  by move/eqP ->; rewrite (class1g (group1 K)).
move => h_n1; move: (centGK h); rewrite !inE h_n1 hK /= => /(_ isT)/subsetP.
move => /(_ (x * t^-1)%g); rewrite inE xtC groupM ?groupV // ?(subsetP sKG) //.
by move => /(_ isT); rewrite groupMr ?groupV // xnK.
Qed.


(* Isaacs 6.34(a2) *)
Lemma irr_induced_Frobenius_ker i : K <| G -> i != 0 ->
  {in K^#, forall x, 'C_G[x] \subset K} -> 'Ind[G, K] 'chi[K]_i \in irr G.
Proof.
move => nKG i_n0 centGK; move/andP: (nKG) => [sKG _].
rewrite char_cfnorm_irrE ?cfInd_char ?irr_char //.
by rewrite induced_prod_index // inertia_Frobenius_ker // indexgg.
Qed.

Lemma eq_irr_diff (a b : nat) (i j r t : Iirr G) :
  (a%:R *: 'chi_i - b%:R *: 'chi_j == a%:R *: 'chi_r - b%:R *: 'chi_t) =
  ((a == 0%N) || (i == r)) && ((b == 0%N) || (j == t)) ||
    ((i == j) && (r == t) && (a == b)).
Proof.
apply/eqP/idP => [| /orP]; last first.
  case; first by move/andP => [/orP] [] /eqP -> /orP [] /eqP ->; rewrite ?scale0r.
  by move/andP => [/andP []] /eqP -> /eqP -> /eqP ->; rewrite !subrr.
move => diff; move: (diff).
move/eqP; rewrite subr_eq addrAC eq_sym subr_eq => /eqP.
move/(congr1 (fun f => '[f, 'chi_i]_G)).
rewrite !cfdotDl !cfdotZl !cfdot_irr eqxx mulr1.
rewrite eq_sym [j == i]eq_sym.
case ir: (_ == _); case ij: (_ == _); case ti: (_ == _); 
  rewrite ?mulr0 ?mulr1 ?addr0 ?add0r ?orbT ?andTb ?andFb ?orbF => /eqP.
- by rewrite (eqP ti) (eqP ij) !eqxx orbT.
- by rewrite eq_sym addrC -subr_eq subrr -(eqN_eqC 0) => /eqP <-; rewrite eqxx.
- by rewrite addrC -subr_eq subrr -(eqN_eqC 0) => /eqP <-; rewrite eqxx.
- move: diff; rewrite (eqP ir) => /addrI /eqP; rewrite eqr_opp eq_scaled_irr.
  by rewrite -(eqN_eqC _ 0) => /andP [].
- rewrite -subr_eq subrr -(eqN_eqC 0) eq_sym => ->.
  by rewrite andTb (eqP ti) (eqP ij) eqxx orbT.
- move/eqP => ba; move: diff; rewrite ba (eqP ij) subrr -scaler_subr => /esym/eqP.
  rewrite scaler_eq0 -(eqN_eqC _ 0); case/orP.
    by move/eqP => a0; move/eqP: ba; rewrite a0 -eqN_eqC andTb => ->.
  by move/eqP: ba; rewrite subr_eq0 -eqN_eqC eq_sym => -> /eqP/chi_inj ->; rewrite andbT eqxx orbT.
- by rewrite -natr_add -(eqN_eqC 0) eq_sym addn_eq0 => /andP [-> ->].
rewrite -(eqN_eqC 0) => /eqP a0; move/eqP: diff.
by rewrite -a0 !scale0r !sub0r eqr_opp eq_scaled_irr -(eqN_eqC _ 0) => /andP [].
Qed.


(* Action of a field automorphism on class functions *)
Section AutomorphismCFun.

Variable u : {rmorphism algC -> algC}.

Lemma rmorph_IntC z : isIntC z -> u z = z.
Proof.
rewrite isIntCE; case/orP; case/isNatCP=> n; first by move ->; rewrite rmorph_nat.
by move/eqP; rewrite eqr_oppC => /eqP ->; rewrite rmorphN rmorph_nat.
Qed.

Lemma cfAutZ_Int z (f : 'CF(G)) : 
  isIntC z -> cfAut u (z *: f) = z *: cfAut u f.
Proof. by move => isZ; rewrite cfAutZ rmorph_IntC. Qed.

Lemma cfAutZ_Nat n (f : 'CF(G)): cfAut u (n%:R *: f) = n%:R *: cfAut u f.
Proof. by apply: cfAutZ_Int; exact: isIntC_nat. Qed.

Lemma cfAut_inj : injective (@cfAut gT G u).
Proof.
move => f g /cfunP => f_e_g; apply/cfunP => x.
by move: (f_e_g x); rewrite !cfunE => /fmorph_inj.
Qed.

Lemma support_cfAut (f : 'CF(G)) (S : {set gT}) : 
  (support f) \subset S -> support (cfAut u f) \subset S.
Proof.
move/subsetP => supp_fS; apply/subsetP => x.
apply: contraR => xnS.
move/contra: (supp_fS x) => /(_ xnS); rewrite inE /= negbK cfunE => /eqP ->.
by rewrite rmorph0.
Qed.

Lemma memc_cfAut S f : f \in 'CF(G, S) -> cfAut u f \in 'CF(G, S).
Proof. by rewrite !cfun_onE; exact: support_cfAut. Qed.

End AutomorphismCFun.

End MoreChar.


(* Additional results about virtual characters *)
Section MoreVChar.

Variable gT : finGroupType.
Variable G : {group gT}.

Lemma isIntC_vchar1 f A : f \in 'Z[irr G, A] -> isIntC (f 1%g).
Proof.
case/vchar_expansion => z int_z; rewrite big_seq => ->.
rewrite sum_cfunE isIntC_sum // => h hZ; rewrite cfunE isIntC_mul //.
case/irrP: hZ => r ->.
by case/isNatCP: (isNatC_irr1 r) => n ->; rewrite isIntC_nat.
Qed.

Section AutomorphismCFun.

Variable u : {rmorphism algC -> algC}.
Implicit Type S : seq 'CF(G).

Local Notation "alpha ^\u" := (cfAut u alpha)
  (at level 2, format "alpha ^\u").

Lemma free_map_auto S : {in S, forall f, f^\u \in S} -> 
  free S -> free (map (cfAut u) S).
Proof.
move => S_inv freeS.
have uniq_uS : uniq (map (cfAut u) S).
  rewrite map_inj_in_uniq ?(uniq_free freeS) //.
  by move => f g _ _; exact: cfAut_inj.
have uS_ieq_S : map (cfAut u) S =i S.
  have sub: {subset (map (cfAut u) S) <= S}.
    by move => f; case/mapP => g gS ->; exact: S_inv.
  have := leq_size_perm uniq_uS sub.
  by rewrite size_map leqnn => /(_ isT) [].
have uS_perm_S : perm_eq (map (cfAut u) S) S.
  by apply: uniq_perm_eq; rewrite ?uniq_uS ?(uniq_free freeS) ?uS_ieq_S.
by rewrite (free_perm_eq uS_perm_S); exact: freeS.
Qed.

Lemma vchar_auto S A (f : 'CF(G)) : 
  free S -> {in S, forall f, f^\u \in S} -> f \in 'Z[S, A] -> f^\u \in 'Z[S, A].
Proof.
rewrite vchar_split => freeS S_inv /andP [fZ supp_f].
rewrite vchar_split memc_cfAut // andbT.
case/vchar_expansion: fZ => z int_z ->.
rewrite rmorph_sum big_seq sum_vchar // => g gS /=.
by rewrite cfAutZ_Int // scale_vchar // mem_vchar // S_inv.
Qed.

Lemma sub_vchar_auto S A f : free S -> {subset S <= irr G} ->
  f \in 'Z[S, A] -> f^\u \in 'Z[S, A] -> f - f^\u \in 'Z[S, A^#].
Proof.
move => freeS sSG.
rewrite vchar_split [f \in _]vchar_split => /andP [fZ supp_f] /andP [fuZ supp_fu].
rewrite vchar_split ?sub_vchar // andTb.
rewrite cfun_onE.
apply/subsetP => x; apply: contraR; rewrite 2!cfunE !inE negb_and negbK.
have fZG : f \in 'Z[irr G] by apply: (vchar_subset (irr_free G) sSG).
case/orP => [/eqP -> | xnA].
  by rewrite cfunE rmorph_IntC ?subrr ?(isIntC_vchar1 fZG).
rewrite !cfun_onE in supp_f supp_fu.
by rewrite (supportP supp_f _ xnA) (supportP supp_fu _ xnA) subr0.
Qed.

End AutomorphismCFun.

Lemma sub_vchar_cconj A f : 
  f \in 'Z[irr G, A] -> f - (f^*)%CF \in 'Z[irr G, A^#].
Proof.
move => fZ; rewrite sub_vchar_auto ?vchar_auto ?irr_free //.
by move => xi /irrP [i] ->; rewrite cfConjC_irr.
Qed.

End MoreVChar.



(* Useful results about the Dade isometry *)
Section MoreDade.

Variable (gT : finGroupType) (G : {group gT}).
Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

Local Notation Atau := (Dade_support ddA).


Lemma Dade0 : 0^\tau = 0.
Proof.
apply/cfunP => x; rewrite !cfunElock.
by case: pickP => //= x0; rewrite cfunE.
Qed.

Lemma Dade_supportJ g : g \in G -> Atau :^ g = Atau.
Proof.
move => gG; rewrite /Atau -bigcupJ; apply: eq_bigr => a aA.
rewrite /Dade_support1 class_supportEl -bigcupJ; apply: eq_bigr => x _.
by rewrite -class_rcoset (rcoset_id gG).
Qed.


Section AutomorphismCFun.

Variable u : {rmorphism algC -> algC}.
Local Notation "alpha ^\u" := (cfAut u alpha)
  (at level 2, format "alpha ^\u").

Lemma Dade_auto alpha : alpha \in 'CF(L, A) ->
  (alpha^\tau) ^\u = (alpha^\u)^\tau.
Proof.
move => alphaC; apply/cfunP => g; rewrite cfunE.
have alphauC := memc_cfAut u alphaC.
case: (boolP (g \in Atau)) => [/bigcupP [] a aA gD1 | gnAtau].
  by rewrite !(DadeE _ aA gD1) cfunE.
rewrite (supportP (support_Dade ddA alpha) _ gnAtau).
by rewrite (supportP (support_Dade ddA (alpha^\u)) _ gnAtau) rmorph0.
Qed.

End AutomorphismCFun.

Lemma Dade_conjC alpha : alpha \in 'CF(L, A) ->
  ((alpha^\tau)^*)%CF = (alpha^*)%CF^\tau.
Proof. by move => alphaC; rewrite Dade_auto. Qed.

End MoreDade.


(* Useful lemmas about (-1)^n *)
Section MoreSign.

Variables (R : ringType) (V : lmodType R).
Implicit Types f g : V.

Lemma sqr_sign n : ((-1 : R) ^+ n) ^+ 2 = 1.
Proof. by rewrite exprnC sqrrN !exp1rn. Qed.

Lemma signr_oppC n (a b : R) : (a == (-1) ^+ n * b) = ((-1) ^+ n * a == b).
Proof. by apply/idP/idP => [/eqP ->|/eqP <-]; rewrite mulrA -expr2 sqr_sign mul1r. Qed.

Lemma scaler_sign_oppC n f g: (f == (-1) ^+ n *: g) = ((-1) ^+ n *: f == g).
Proof. by apply/idP/idP=> [/eqP ->|/eqP <-]; rewrite scalerA -expr2 sqr_sign scale1r. Qed.

End MoreSign.


(* Results about the set of induced irriducible characters *)
Section InducedIrrs.

Variable gT : finGroupType.
Variables K L : {group gT}.
Hypothesis nKL : K <| L.

Let e := #|L : K|%:R : algC.

(* The set of all induced irreducible characters *)
Definition induced_irrs := undup (map ('Ind[L, K]) (irr K)).

Lemma uniq_ind_irrs : uniq (induced_irrs).
Proof. exact: undup_uniq. Qed.

Lemma ind_irrsP t : 
  reflect (exists r : Iirr K, t = 'Ind[L, K] 'chi_r) (t \in induced_irrs).
Proof.
apply: (iffP idP); rewrite mem_undup.
  by case/mapP => f; case/irrP => r -> ->; exists r.
by case => r ->; apply/mapP; exists 'chi_r => //; exact: irr_chi.
Qed.

Lemma ind_irrs_size_gt0 : (0 < size induced_irrs)%N.
Proof.
case nn: (size induced_irrs); last by [].
have: ('Ind[L, K] 'chi[K]_0 \in induced_irrs) by apply/ind_irrsP; exists 0.
by rewrite (size0nil nn) in_nil.
Qed.

Lemma memc_ind_irrs : {subset induced_irrs <= 'CF(L, K)}.
Proof. by move => f; case/ind_irrsP => r ->; exact: cfInd_normal. Qed.

Lemma ind_irrs_1neq0 f : f \in induced_irrs -> f 1%g != 0.
Proof.
case/ind_irrsP => r ->; rewrite cfInd1 ?normal_sub //. 
by rewrite ?mulf_neq0 ?irr1_neq0 ?neq0GiC.
Qed.

Lemma ind_irrs_norm_neq0 f : f \in induced_irrs -> '[f]_L != 0.
Proof.
move => f_ind; case eq0: ('[_, _]_L == 0); last by [].
move: eq0; rewrite cfnorm_eq0 => /eqP f0.
by move: (ind_irrs_1neq0 f_ind); rewrite f0 cfunE eqxx.
Qed.

Lemma ind_irrs_orthogonal : pairwise_orthogonal induced_irrs.
Proof.
apply/pairwise_orthogonalP; split.
  rewrite cons_uniq uniq_ind_irrs andbT.
  apply: contraT; rewrite negbK => /ind_irrsP [r] /esym/eqP.
  rewrite cfInd_eq0 ?irr_char ?normal_sub // => /eqP/cfunP /(_ 1%g) chi1_0.
  by move: (irr1_neq0 r); rewrite chi1_0 cfunE eqxx.
move => f g; case/ind_irrsP => r ->; case/ind_irrsP => t -> {f g}.
have := cfclass_irr_induced r t nKL.
by case: (_ \in _) => //; move ->; rewrite eqxx.
Qed.

Lemma ind_irrs_ortho f g : f \in induced_irrs -> g \in induced_irrs -> 
  f != g -> '[f, g]_L = 0.
Proof.
move => fZ gZ fng; case/pairwise_orthogonalP: ind_irrs_orthogonal.
by move => _ /(_ f g fZ gZ fng).
Qed.

Lemma one_in_ind_irrs : 'Ind[L, K] 1 \in induced_irrs.
Proof. by apply/ind_irrsP; exists 0; rewrite chi0_1. Qed.

Lemma free_ind_irrs : free induced_irrs.
Proof. exact: (orthogonal_free ind_irrs_orthogonal). Qed.

Lemma ind_irrs_1Z f : f \in induced_irrs -> isIntC (f 1%g).
Proof.
case/ind_irrsP => r ->.
by rewrite cfInd1 ?normal_sub // isIntC_mul ?isIntC_nat ?isIntCE ?isNatC_irr1.
Qed.


(* The set of induced irreducible characters without 'Ind[L, K] '1_K *)
Definition induced_irrs1 := filter (predC1 ('Ind[L, K] 1)) induced_irrs.

Lemma ind_irrs1_rem : induced_irrs1 = rem ('Ind[L, K] 1) induced_irrs.
Proof. by rewrite rem_filter ?uniq_ind_irrs. Qed.

Lemma ind_irrs1P t : reflect (exists2 r : Iirr K, t = 'Ind[L, K] 'chi_r &
  t != 'Ind[L, K] 1) (t \in induced_irrs1).
Proof.
rewrite mem_filter; apply: (iffP andP) => /=.
  by move => [t_n_1] /ind_irrsP [r] t_eq; exists r; rewrite t_eq in t_n_1 *.
by case => r -> ->; split => //; apply/ind_irrsP; exists r.
Qed.

Lemma ind_irrs1_subset : {subset induced_irrs1 <= induced_irrs}.
Proof. by move => f; rewrite mem_filter => /andP []. Qed.

Lemma memcW_ind_irrs1 : {subset induced_irrs1 <= 'CF(L)}.  
Proof. by move => f/ind_irrs1_subset/memc_ind_irrs. Qed.

Lemma support_ind_irrs1 f : f \in induced_irrs1 -> support f \subset K.
Proof. by move/ind_irrs1_subset/memc_ind_irrs; rewrite cfun_onE. Qed.

Lemma memc_ind_irrs1 : {subset induced_irrs1 <= 'CF(L, K)}.
Proof. by move => f /ind_irrs1_subset/memc_ind_irrs. Qed.

Lemma uniq_ind_irrs1 : uniq induced_irrs1.
Proof. by apply: filter_uniq; exact: uniq_ind_irrs. Qed.

Lemma free_ind_irrs1 : free induced_irrs1.
Proof. apply: free_filter; exact: free_ind_irrs. Qed.

Lemma ind_irrs1_vcharW : {subset induced_irrs1 <= 'Z[induced_irrs1]}.
Proof. by move => f fS; rewrite mem_vchar // free_ind_irrs1. Qed.

Lemma ind_irrs1_vchar : {subset induced_irrs1 <= 'Z[induced_irrs1, K]}.
Proof. by move => f fS; rewrite vchar_split ind_irrs1_vcharW ?memc_ind_irrs1. Qed.

Lemma ind_irrs1_orthogonal : pairwise_orthogonal induced_irrs1.
Proof.
exact: (sub_pairwise_orthogonal ind_irrs1_subset uniq_ind_irrs1 ind_irrs_orthogonal).
Qed.

Lemma ind_irrs1_ortho : 
  {in induced_irrs1 &, forall f g, f != g -> '[f, g]_L = 0}.
Proof.
move => f g /ind_irrs1_subset f_ind /ind_irrs1_subset g_ind.
exact: ind_irrs_ortho.
Qed.

Lemma ind_irrs1_ortho_ind1 : {in induced_irrs1, forall f, '[f, 'Ind[L, K] 1]_L = 0}.
Proof. 
move => f /ind_irrs1P [r] ->; apply: ind_irrs_ortho; apply/ind_irrsP.
  by exists r.
by exists 0; rewrite chi0_1.
Qed.

Lemma ind_irrs1_ortho1K : {in induced_irrs1, forall f, '[f, '1_K]_L = 0}.
Proof.
move => f /ind_irrs1_ortho_ind1; rewrite cfInd_cfun1 // cfdotZr => /eqP.
by rewrite mulf_eq0 conjC_eq0 (negPf (neq0GiC _ _)) orFb => /eqP.
Qed.

Lemma ind_irrs1_ortho1 : {in induced_irrs1, forall f, '[f, 1]_L = 0}.
Proof.
move => f /ind_irrs1P [r] -> f_n_1.
rewrite -Frobenius_reciprocity cfRes_cfun1 ?normal_sub // -chi0_1 cfdot_irr.
by case r0: (_ == _) => //; move: f_n_1; rewrite (eqP r0) chi0_1 eqxx.
Qed.

Lemma ind_irrs1_1eZ f : f \in induced_irrs1 -> isIntC (f 1%g / e).
Proof.
case/ind_irrs1P => r -> _; rewrite cfInd1 ?normal_sub //.
by rewrite mulrAC mulfV ?neq0GiC // mul1r isIntCE isNatC_irr1.
Qed.

Lemma ind_irrs1_sub_vchar f g : f \in induced_irrs1 -> g \in induced_irrs1 ->
  g 1%g *: f - f 1%g *: g \in 'Z[induced_irrs1, K^#].
Proof.
move => fS gS; rewrite vchar_split cfun_onE.
rewrite sub_vchar ?scale_vchar ?ind_irrs1_vcharW ?ind_irrs_1Z ?ind_irrs1_subset //.
rewrite andTb; apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK]; first by rewrite mulrC subrr.
by rewrite !(supportP (support_ind_irrs1 _) _ xnK) // !mulr0 subr0.
Qed.

Lemma ind_irrs1_sub_memc f g : f \in induced_irrs1 -> g \in induced_irrs1 ->
  g 1%g *: f - f 1%g *: g \in 'CF(L, K^#).
Proof.
by move => fS gS; rewrite cfun_onE (support_vchar (ind_irrs1_sub_vchar fS gS)).
Qed.

Lemma ind_irrs1_conjC : 
  {in induced_irrs1, forall f, (f^*)%CF \in induced_irrs1}.
Proof.
move => f /ind_irrs1P [r] -> f_n_1.
apply/ind_irrs1P; case/irrP: (cfConjC_irr r) => t tr.
exists t; rewrite conj_cfInd ?tr //.
apply: contra f_n_1 => /eqP eq1; rewrite -(cfConjCK ('Ind[L, K] ('chi_r))).
by rewrite conj_cfInd tr eq1 conj_cfInd cfConjC1.
Qed.

Lemma ind_irrs1_sub_conjC_vchar : 
  {in induced_irrs1, forall f, f - (f^*)%CF \in 'Z[induced_irrs1, K^#]}.
Proof.
move => f fS /=.
rewrite vchar_split sub_vchar ?ind_irrs1_vcharW ?ind_irrs1_conjC // andTb cfun_onE.
apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK].
  by rewrite isIntC_conj ?subrr // ind_irrs_1Z ?ind_irrs1_subset.
by rewrite (supportP (support_ind_irrs1 fS) _ xnK) conjC0 subr0.
Qed.

Lemma ind_irrs1_conjC_ortho : 
  odd #|L| -> {in induced_irrs1, forall f, '[f, (f^*)%CF]_L = 0}.
Proof.
move => oddL f fS.
case/ind_irrs1P: fS => r -> f_n_1.
rewrite odd_induced_orthogonal //.
by apply: contra f_n_1 => /eqP ->; rewrite chi0_1.
Qed.

Lemma ind_irrs1_conjC_neq : 
  odd #|L| -> {in induced_irrs1, forall f, (f^*)%CF != f}.
Proof.
move => oddL f fS.
have := ind_irrs_norm_neq0 (ind_irrs1_subset fS).
by apply: contra => /eqP {2}<-; rewrite ind_irrs1_conjC_ortho.
Qed.

Lemma ind_irrs1_conjC_ortho2 r : odd #|L| -> 'chi[L]_r \in induced_irrs1 ->
  orthonormal [:: 'chi_r; (('chi_r)^*)%CF].
Proof.
move => oddL xiS.
apply/orthonormal2P.
by rewrite ind_irrs1_conjC_ortho // -conjC_IirrE !cfdot_irr !eqxx.
Qed.


(* Lemmas about sums of squares of values of induced characters at 1 *)
Section SumLemma.

Let inv_ind (f : 'CF(L)) : Iirr K :=
  odflt 0 [pick r | 'Ind[L, K] 'chi[K]_r == f].

Let zi := induced_irrs.
Let n := size zi.

Let cconj_sum (F : ('CF(L) * 'CF(K)) -> algC) :
\sum_(i < Nirr K) F ('Ind[L, K] 'chi_i, 'chi_i) = 
\sum_(i < n) \sum_(f <- ('chi_(inv_ind zi`_i) ^: L)%CF) F (zi`_i, f).
Proof.
pose alpha f := ('Ind[L, K] f, f).
transitivity (\sum_(p <- map alpha (irr K)) F p).
  rewrite big_map [in X in _ = X](big_nth 0) big_mkord size_tuple.
  by apply: eq_bigr => i _; rewrite /alpha (tnth_nth 0).
transitivity (\sum_(p <- map alpha (irr K)) \sum_(i < n | p.1 == zi`_i) F p).
  rewrite big_seq_cond [in X in _ = X]big_seq_cond.
  apply: eq_bigr => f /andP [f_map _].
  set rhs := \sum_(i < n | _) _.
  have {rhs}->: rhs = \sum_(x <- zi | x == f.1) F f.
    rewrite (big_nth 0) big_mkord.
    by apply: eq_bigl => x; rewrite eq_sym.
  rewrite big_pred1_uniq ?uniq_ind_irrs //.
  apply/ind_irrsP; case/mapP: f_map => a; case/irrP => t -> ->.
  by exists t.
rewrite (big_nth (0, 0)) big_mkord size_map size_tuple.
pose ss := map alpha (irr K).
rewrite -/ss (exchange_big_dep predT) //=.
apply: eq_bigr => i _.
rewrite -cfclass_sum ?nKL //=.
have nth_ss (j : Iirr K) : nth (0, 0) ss j = ('Ind[L, K] 'chi_j, 'chi_j).
  by rewrite (nth_map 'chi[K]_0) ?size_tuple ?ltn_ord // -tnth_nth.
apply: congr_big => //; last first.
  by move => j; rewrite nth_ss => /= /eqP ->.
move => j; rewrite /= nth_ss /=.
have inv (t : Iirr K) : 'Ind[L, K] 'chi_(inv_ind ('Ind[L, K] 'chi_t)) = 'Ind[L, K] 'chi_t.
  rewrite /inv_ind; case: pickP => [x /eqP | ] //=.
  by move => /(_ t); rewrite eqxx.
have in_zi: zi`_i \in zi by exact: mem_nth.
apply/eqP/idP; last first.
  move => hyp.
  have := cfclass_irr_induced (inv_ind zi`_i) j nKL.
  by rewrite hyp; case: (ind_irrsP _ in_zi) => t ->; rewrite inv => ->.
case: (ind_irrsP _ in_zi) => t ->.
case hyp: (_ \in _); first by []; move => jt.
have := cfclass_irr_induced (inv_ind ('Ind[L, K] 'chi_t)) j nKL.
rewrite hyp inv jt => /eqP.
rewrite cfnorm_eq0 => /eqP/cfunP /(_ 1%g).
rewrite cfunE cfInd1 ?normal_sub // => /eqP; rewrite mulf_eq0.
rewrite (negPf (neq0GiC _ _)) orFb => /eqP contr.
by have := irr1_neq0 t; rewrite contr eqxx.
Qed.

Lemma ind_irrs_sum1 : \sum_(f <- induced_irrs) (f 1%g / e) ^+ 2 / '[f]_L = 
  #|K|%:R / e.
Proof.
rewrite -irr_sum_square mulrC.
apply/(mulfI (neq0GiC L K)); rewrite -/e mulrA mulfV ?neq0GiC // mul1r -mulr_sumr.
rewrite (big_nth 0) big_mkord -/n.
set S1 := \sum_(i < n) _.
set S2 := \sum_(i < Nirr K) _.
have := cconj_sum (fun (p : 'CF(L) * 'CF(K)) => (p.2 1%g) ^+ 2).
set S3 := \sum_(i < Nirr K) _.
have ->: S3 = S2 by apply: eq_bigr => i _ /=.
move ->; apply: eq_bigr => i _.
set t := inv_ind _.
have in_zi : zi`_i \in zi by exact: mem_nth.
have zi_t: zi`_i = 'Ind[L, K] 'chi_t.
  rewrite /t /inv_ind; case: pickP => /=; first by move => r /eqP ->.
  by case: (ind_irrsP _ in_zi) => j -> /(_ j); rewrite eqxx.
rewrite expr2 mulrCA !mulrA divfK ?neq0GiC //.
rewrite -[_ / e]mulrC -!mulrA.
apply/(mulfI (neq0GiC L K)); rewrite !mulrA mulfV ?neq0GiC // mul1r.
have := induced_sum_rcosets1 t nKL => /=; rewrite -zi_t.
move/cfunP => /(_ 1%g).
rewrite !cfunE sum_cfunE -/e -/zi cfRes1 ?normal_sub // mulrAC => ->.
congr (_ * _); apply: eq_bigr => f => f_conj.
by rewrite cfunE expr2.
Qed.

Lemma ind_irrs1_sum1 : \sum_(f <- induced_irrs1) (f 1%g / e) ^+ 2 / '[f]_L =
  (#|K|%:R - 1) / e.
Proof.
have := ind_irrs_sum1.
rewrite (big_rem _ one_in_ind_irrs) /= -ind_irrs1_rem.
rewrite cfnorm_Ind1 // cfInd1 ?normal_sub // cfun1E in_group.
rewrite mulr1 mulfV ?neq0GiC // expr2 mulr1.
by move/eqP; rewrite eq_sym addrC -subr_eq -mulr_subl => /eqP ->.
Qed.

End SumLemma.

End InducedIrrs.


Section InducedIrrsKer.

Variable gT : finGroupType.
Implicit Types (K L : {group gT}) (A : {set gT}).

(* The set of all induced irreducible characters with the given kernels *)
Definition induced_irrs_ker K L A := undup (map ('Ind[L, K]) 
  (filter [pred f | A \subset cfker f] (irr K))).

Definition induced_irrs1_ker K L A := 
  filter (predC1 ('Ind[L, K] 1)) (induced_irrs_ker K L A).

Lemma ind_irrs_kerP K L A t :
  reflect (exists2 r : Iirr K, t = 'Ind[L, K] 'chi_r & A \subset cfker 'chi_r)
  (t \in induced_irrs_ker K L A).
Proof.
apply: (iffP idP); rewrite mem_undup.
  case/mapP => f; rewrite mem_filter /= => /andP [sAker].
  by case/irrP => r f_irr ->; exists r; rewrite -f_irr.
case => r -> sAker; apply/mapP; exists 'chi_r => //.
by rewrite mem_filter irr_chi /= sAker.
Qed.

Lemma ind_irrs_ker_sub K L A : {subset induced_irrs_ker K L A <= induced_irrs K L}.
Proof. by move => f /ind_irrs_kerP [r -> _]; apply/ind_irrsP; exists r. Qed.

Lemma ind_irrs1_ker_sub K L A : {subset induced_irrs1_ker K L A <= induced_irrs1 K L}.
Proof. by move => f; rewrite !mem_filter => /andP [->] /ind_irrs_ker_sub ->. Qed.

Lemma ind_irrs1_kerP K L A t : 
  reflect (exists r : Iirr K, [/\ t = 'Ind[L, K] 'chi_r,
    t != 'Ind[L, K] 1 & A \subset cfker 'chi_r]) 
  (t \in induced_irrs1_ker K L A).
Proof.
rewrite mem_filter; apply: (iffP andP) => /=.
  by move => [t_n_1] /ind_irrs_kerP [r] t_eq sAker; exists r; rewrite -t_eq.
case => r [] -> -> sAker; apply/andP; rewrite andTb.
by apply/ind_irrs_kerP; exists r.
Qed.

Lemma free_ind_irrs1_ker K L A : K <| L -> free (induced_irrs1_ker K L A).
Proof.
move => nKL; apply: (@orthogonal_free _ L).
apply: (sub_pairwise_orthogonal _ _ (ind_irrs1_orthogonal nKL)).
  exact: ind_irrs1_ker_sub.
by rewrite filter_uniq ?undup_uniq.
Qed.

Lemma ind_irrs1_ker_Z_sub K L A X : K <| L ->
  {subset 'Z[induced_irrs1_ker K L A, X] <= 'Z[induced_irrs1 K L, X]}.
Proof.
move => nKL.
apply: vchar_subset; rewrite ?free_ind_irrs1_ker ?free_ind_irrs1 //.
exact: ind_irrs1_ker_sub.
Qed.

Lemma conjC_eq a b : (a^* == b^*) = (a == b).
Proof.
apply/idP/idP; last by move/eqP ->.
by move/eqP/fmorph_inj ->.
Qed.

Lemma cfker_conjC K (chi : 'CF(K)) : cfker chi^* = cfker chi.
Proof.
rewrite /cfker -setP => x; rewrite !inE.
case: (x \in K); rewrite !(andTb, andFb) //.
by apply/forallP/forallP => H y; move: (H y); rewrite !cfunE conjC_eq.
Qed.

Lemma ind_irrs1_ker_conjC K L A : 
  {in induced_irrs1_ker K L A, forall f : 'CF(L), 
    (f^*)%CF \in induced_irrs1_ker K L A}.
Proof.
move => f /ind_irrs1_kerP [r] [-> f_n_1 sAker].
apply/ind_irrs1_kerP; exists (conjC_Iirr r).
rewrite conj_cfInd conjC_IirrE cfker_conjC; split => //.
apply: contra f_n_1 => /eqP eq1.
by rewrite -(cfConjCK ('Ind[L] 'chi_r)) conj_cfInd eq1 conj_cfInd cfConjC1.
Qed.

Lemma norm_qfunc (A K : {group gT}) (chi : 'CF(K)) : 
  A <| K -> is_char chi -> A \subset cfker chi ->
    '[(chi / A)%CF] = '[chi].
Proof.
move => nAK char_chi sAker.
rewrite !cfdotE card_quotient ?normal_norm //.
apply/(mulfI (neq0GC K)); rewrite !mulrA mulfV ?neq0GC // mul1r.
rewrite -(LaGrange (normal_sub nAK)) natr_mul mulfK -?neq0N_neqC -?lt0n ?indexg_gt0 //.
apply/esym.
rewrite (partition_big_imset (coset A)) /=.
rewrite -morphimEsub ?normal_norm //= -quotientE -mulr_sumr.
apply: eq_bigr => c.
rewrite {1}quotientE => /imsetP [y]; rewrite inE => /andP [yNA yK] /= -> {c}.
rewrite (big_setIDdep _ _ (A :* y)) /= addrC big_pred0 ?add0r; last first.
  move => x /=; rewrite !inE.
  case xAy: (x \in _) => //; case xK: (x \in K) => //.
  rewrite andTb; apply: contraFF xAy.
  move/eqP/rcoset_kercosetP; apply => //.
  by apply: (subsetP (normal_norm nAK)).
rewrite (setIidPr _); last first.
  apply/subsetP => x /rcosetP [a aA ->]; rewrite groupM //.
  exact: (subsetP (normal_sub nAK) a aA).
rewrite -(card_rcoset _ y) -sum1_card natr_sum -mulr_suml.
apply: congr_big => // g.
  case gAy: (g \in _) => //; rewrite andTb.
  apply/eqP; apply/rcoset_kercosetP => //; apply: (subsetP (normal_norm nAK)).
  by case/rcosetP: gAy => x xA ->; rewrite groupM // (subsetP (normal_sub nAK)).
move => /andP [gAy /eqP <-].
rewrite -(cfQuoE nAK) ?mul1r //.
case/rcosetP: gAy => x xA ->; rewrite groupM //.
exact: (subsetP (normal_sub nAK) x xA).
Qed.


Section SumLemma.

Variables K L A : {group gT}.
Hypotheses (nKL : K <| L) (nAL : A <| L) (sAK : A \subset K).

Let nAK : A <| K. Proof. by apply: (normalS sAK _ nAL); exact: normal_sub. Qed.

Lemma map_ind_irrs_ker : 
  perm_eq (map (cfQuo A) (induced_irrs_ker K L A))
  (induced_irrs (K / A) (L / A)).
Proof.
rewrite uniq_perm_eq ?uniq_ind_irrs //.
  rewrite map_inj_in_uniq ?undup_uniq //.
  move => f g /ind_irrs_kerP [r -> sAr] /ind_irrs_kerP [t -> sAt].
  move/(congr1 (@cfMod _ _ A)).
  by rewrite !(cfQuoK nAL) // -cfker_induced_irr_sub.
move => f; apply/mapP/ind_irrsP.
  move => [g] /ind_irrs_kerP [r -> sAker] ->.
  rewrite -induced_quotientE //.
  by case/irrP: (cfQuo_irr nAK sAker) => t ->; exists t.
case => r ->.
exists ('Ind[L, K] ('chi_r %% A)%CF).
  apply/ind_irrs_kerP.
  by exists (mod_Iirr r); rewrite !mod_IirrE // cfker_Mod.
by rewrite -mod_IirrE // -induced_quotientE ?mod_IirrE ?cfker_Mod // cfModK.
Qed.

Lemma ind_irrs_ker_sum1 : 
  \sum_(f <- induced_irrs_ker K L A) (f 1%g) ^+ 2 / '[f]_L = #|L : A|%:R.
Proof.
have := ind_irrs_sum1 (quotient_normal A nKL).
rewrite index_quotient_eq ?(normal_sub nKL) ?(normal_norm nAL) ?subIset ?sAK ?orbT //.
set e := #|_ : _|%:R.
have e_n0 : e != 0 by rewrite -neq0N_neqC -lt0n indexg_gt0.
do 2 move/(congr1 (fun x => x * e)).
rewrite divfK // -!mulr_suml.
rewrite -natr_mul card_quotient ?normal_norm // mulnC LaGrange_index ?normal_sub //.
move <-.
rewrite -(eq_big_perm _ map_ind_irrs_ker) /= big_map.
rewrite big_seq [in X in _ = X]big_seq.
apply: eq_bigr => f /ind_irrs_kerP [r] ->.
rewrite (cfker_induced_irr_sub _ nKL) // => sAker; apply/esym.
rewrite exprn_mull -!mulrA mulrA [in X in _ = X]mulrA -!expr2.
congr (_ ^+ 2 * _); first by rewrite -(coset_id (group1 A)) cfQuoE.
rewrite mulrA mulrC expr2 !mulrA !mulfK //.
by rewrite norm_qfunc // cfInd_char ?irr_char.
Qed.

Lemma ind_irrs1_ker_sum1 :
  \sum_(f <- induced_irrs1_ker K L A) (f 1%g)^+2 / '[f]_L = 
  #|L : K|%:R * (#|K : A|%:R - 1).
Proof.
have := ind_irrs_ker_sum1.
rewrite (bigID (pred1 ('Ind[L, K] 1))) /= big_pred1_uniq ?undup_uniq //; last first.
  by apply/ind_irrs_kerP; exists 0; rewrite chi0_1 // cfker_cfun1.
rewrite -big_filter => /eqP; rewrite eq_sym addrC -subr_eq => /eqP <-.
rewrite cfnorm_Ind1 // cfInd_cfun1 // cfunE cfuniE // in_group mulr1.
rewrite expr2 mulfK; last by rewrite -neq0N_neqC -lt0n indexg_gt0.
by rewrite mulr_subr -natr_mul LaGrange_index ?normal_sub // mulr1.
Qed.
  
End SumLemma.

End InducedIrrsKer.



(* The main section *)
Section Six.

Variable gT : finGroupType.
Variable G : {group gT}.


Lemma realC_neg_lt x y : isRealC x -> isRealC y -> ~~(x < y) = (y <= x).
Proof.
move => r_x r_y.
apply/negPf/idP; last first.
  by move/leC_gtF.
move => xy_f.
have : isRealC (x - y).
  by rewrite /isRealC rmorph_sub (eqP r_x) (eqP r_y).
move/realC_leP; case; rewrite ?leC_sub //.
rewrite -posC_opp oppr_add opprK addrC leC_sub leC_eqVlt xy_f orbF.
by move/eqP ->; exact: leC_refl.
Qed.

Lemma subsetDD1 (X Y : {set gT}) a : X \subset Y -> X :\ a \subset Y :\ a.
Proof.
rewrite subsetD1 !inE negb_and negbK eqxx orTb andbT.
exact: (subset_trans (subD1set X a)).
Qed.


(* PF 6.1 *)
Section PF61.

Variables K L : {group gT}.
Variable R : 'CF(L) -> seq 'CF(G).
Variable tau : {linear 'CF(L) -> 'CF(G)}.

Local Notation calS := (induced_irrs1 K L).

Hypothesis isoL : {in 'Z[calS, L^#] &, isometry tau}.
Hypothesis precoherentS : subcoherent calS tau R.

Hypothesis nKL : K <| L.
Hypothesis solvableK : solvable K.

(* PF 6.2 *)
Section PF62.

Variables A B C D : {group gT}.

Hypotheses (nAL : A <| L) (nBL : B <| L) (nCL : C <| L) (nDL : D <| L).
Hypotheses (pAK : A \proper K) (sBK : B \subset K).
Hypotheses (sBD: B \subset D) (sDC: D \subset C) (sCK : C \subset K).
Hypothesis sDB_ZCB : (D / B)%g \subset 'Z((C / B)%g).

Local Notation SS X := (induced_irrs1_ker K L X).

Hypothesis coherentSA : coherent (SS A) L^# tau.
Hypothesis not_coherentSB : ~ coherent (SS B) L^# tau.

(******************************)

Let sKL : K \subset L. Proof. exact: normal_sub. Qed.
Let sAK : A \subset K. Proof. by move/andP: pAK => []. Qed.
Let nAK : A <| K. Proof. by rewrite (normalS _ _ nAL) // ?normal_sub. Qed.
Let nBK : B <| K. Proof. rewrite (normalS _ _ nBL) // ?normal_sub. Qed.

(* Preliminary results *)
Lemma cfQuo_cfun1 (X : {group gT}) : X <| K -> (1 / X)%CF = (1 : 'CF(K / X)).
Proof.
move => nXK; apply/cfunP => x.
rewrite cfunElock !cfun1E nXK cfker_cfun1 (normal_sub nXK) andTb mulr1n.
apply/eqP; rewrite -eqN_eqC; apply/eqP; (congr (nat_of_bool _)).
apply/idP/idP => xK.
  move/coset_mem: (mem_repr_coset x) => <-.
  by apply/imsetP => /=; exists (repr x); rewrite ?(setIidPr _) ?xK // normal_norm.
move/imsetP: xK => /= [y]; rewrite inE => /andP [_ yK] ->.
have := mem_repr_coset (coset X y).
rewrite val_coset; last exact: (subsetP (normal_norm nXK)).
by case/rcosetP => z zA ->; rewrite groupM // (subsetP (normal_sub nXK)).
Qed.


Let exists_phi (X : {group gT}) : X \proper K -> X <| K ->
  exists2 phi, phi \in SS X & phi 1%g = #|L : K|%:R.
Proof.
move => pXK nXK.
have KXn1 : (K / X)%g != 1%g.
  rewrite -subG1 quotient_sub1 ?normal_norm //.
  by move/andP: pXK => [].
case: (lin_char_solvable KXn1 (quotient_sol X solvableK)) => r /andP [_ r1] rn1.
exists ('Ind[L, K] ('chi_r %% X)%CF); last first.
  by rewrite cfInd1 // cfModE // coset_id ?in_group // (eqP r1) mulr1.
apply/ind_irrs1_kerP; exists (mod_Iirr r).
rewrite -mod_IirrE //; split => //; last first.
  by rewrite mod_IirrE // cfker_Mod.
apply: contra rn1 => /eqP => ind_eq.
have := cfclass_irr_induced 0 (mod_Iirr r) nKL.
rewrite ind_eq.
case chi_in : (_ \in _); last first.
  by move/eqP; rewrite chi0_1 cfnorm_eq0 cfInd_eq0 ?cfun1_char // (negPf (nonzero1r _)).
move => _; move: chi_in.
rewrite chi0_1 cfclass1 // inE mod_IirrE //.
move/eqP/(congr1 (@cfQuo _ _ X)).
by rewrite cfModK // cfQuo_cfun1 // => ->.
Qed.

Let conjC_closed_SX X : conjC_closed (SS X).
Proof.
move => f fS /=; rewrite !inE.
rewrite (ind_irrs1_ker_conjC fS) andbT.
move/ind_irrs1_ker_sub: fS => fS.
by case: precoherentS => [[]] _ /(_ f fS); rewrite !inE => /andP [].
Qed.

Let sZAB X : {subset 'Z[SS B, X] <= 'Z[undup (SS A ++ SS B), X]}.
Proof.
apply: vchar_subset; rewrite ?free_ind_irrs1_ker //; last first.
  by move => x; rewrite mem_undup mem_cat => ->; rewrite orbT.
apply: (@orthogonal_free _ L).
apply: (sub_pairwise_orthogonal _ _ (ind_irrs_orthogonal nKL)).
  move => x; rewrite mem_undup mem_cat.
  by case/orP; case/ind_irrs1_kerP => r [-> _ _]; apply/ind_irrsP; exists r.
exact: undup_uniq.
Qed.


Lemma perm_eq_coherent l1 l2 X : perm_eq l1 l2 -> free l1 -> 
  coherent l1 X tau -> coherent l2 X tau.
Proof.
move => peq12 free1.
have ZX Y: 'Z[l1, Y] =i 'Z[l2, Y].
  move => f; apply/idP/idP => fZ.
    rewrite (@vchar_subset _ _ l1 l2) -?(free_perm_eq peq12) // => x.
    by rewrite (perm_eq_mem peq12).
  rewrite (@vchar_subset _ _ l2 l1) -?(free_perm_eq peq12) // => x.
  by rewrite (perm_eq_mem peq12).
case => [tau1] [] isom to tau_eq.
exists tau1; try split.
- by move => f g; rewrite -!ZX; exact: isom.
- by move => f; rewrite -ZX; exact: to.
by move => f; rewrite -ZX; exact: tau_eq.
Qed.


(* PF 6.2 *)
Let ineq1_neg : (forallb i : ordinal (size (SS B)),
  let psi := tnth (in_tuple (SS B)) i in
    2%:R * psi 1%g * #|L : K|%:R < \sum_(f <- SS A) (f 1%g)^+2 / '[f]_L) ->
  (forall S1, uniq S1 -> conjC_closed S1 -> {subset SS A <= S1} -> 
    {subset S1 <= undup (SS A ++ SS B)} -> 
    coherent S1 L^# tau).
Proof.
move/forallP => ineq.
have : forall T P, (forall n : nat, forall (l : seq T), 
  (size l <= n)%N -> P l) -> forall (l : seq T), P l.
  by move => T P cond l; apply: (cond (size l)); exact: leqnn.
apply.
elim => [l | n].
  rewrite leqn0 size_eq0 => /eqP -> /=.
  by case: (exists_phi pAK nAK) => f fS _ _ _ /(_ f fS); rewrite in_nil.
move => IH l.
case: (leqP (size l) n).
  by move => size_l _ uniq_l c_l s_l s_l2; apply: IH.
move => le1 le2.
have {le1} {le2}: size l = n.+1.
  by apply: anti_leq; rewrite le1 le2.
move => size_l uniq_l conj_l sAl slAB.
case: (leqP (size l) (size (SS A))).
  move => size_le.
  apply: (perm_eq_coherent _ _ coherentSA); last by rewrite free_ind_irrs1_ker.
  suff: SS A =i l /\ size (SS A) = size l.
    move => [eq_i eq_size].
    apply: uniq_perm_eq => //.
    by rewrite uniq_free ?free_ind_irrs1_ker.
  apply: leq_size_perm => //.
  by rewrite uniq_free ?free_ind_irrs1_ker.
move => size_gt.
have [psi psi_l psi_nA] : exists2 psi, psi \in l & psi \notin SS A.
  case c: (forallb i : ordinal (size l), nth 0 l i \in SS A).
    move/forallP: c => c.
    suff: l =i SS A /\ size l = size (SS A).
      move => [_] size_eq; move: size_gt; rewrite ltn_neqAle => /andP [].
      by rewrite size_eq eqxx.
    apply: leq_size_perm => //; last by rewrite ltnW.
    move => x xl; move: (xl); rewrite -index_mem => index_x.
    pose i := Ordinal index_x; move: (c i).
    have ->: nat_of_ord i = index x l by [].
    by rewrite nth_index.
  move/negP/negP: c; rewrite negb_forall => /existsP [i li].
  by exists l`_i => //; rewrite mem_nth ?ltn_ord.
have slS : {subset l <= calS}.
  move => f /slAB; rewrite mem_undup mem_cat.
  by case/orP => /ind_irrs1_ker_sub.
pose l1 := filter (predC1 (psi^*)%CF) (filter (predC1 psi) l).
pose ll := [:: psi, (psi^*)%CF & l1].
have cpsi_l : (psi^*)%CF \in filter (predC1 psi) l.
  by rewrite mem_filter /=; move: (conj_l psi psi_l); rewrite !inE.
have uniq_ll: uniq ll.
  rewrite !cons_uniq /= inE !filter_uniq // negb_or andbT.
  rewrite !mem_filter /= !negb_and !negbK !eqxx !orTb orbT !andbT.
  by move: (conj_l psi psi_l); rewrite !inE eq_sym => /andP [].
have p_eq: perm_eq ll l.
  suff: ll =i l /\ size ll = size l.
    by move => [i_eq size_eq]; apply: uniq_perm_eq.
  apply: leq_size_perm => //.
    move => f; rewrite !inE !mem_filter !inE.
    case/orP; first by move/eqP ->.
    case/orP; last by move => /and3P [].
    move => /eqP ->.
    by move: cpsi_l; rewrite mem_filter => /andP [].
  rewrite /ll /l1 /= -rem_filter ?filter_uniq // size_rem //.
  rewrite -rem_filter // size_rem // -subn2 -addn2.
  suff: (2 <= size l)%N by move/subnK ->; exact: leqnn.
  case: (ltngtP 1%N (size l)) => //.
    rewrite -addn1 -{2}[1%N]addn1 leq_add2r leqn0 size_eq0 => /eqP l_nil.
    by move: psi_l; rewrite l_nil in_nil.
  move => size_l1.
  have: size (filter (predC1 psi) l) == 0%N.
    by rewrite -rem_filter // size_rem // -size_l1.
  rewrite size_eq0 => /eqP l_nil.
  by move: cpsi_l; rewrite l_nil in_nil.
have free_ll : free ll.
  rewrite (free_perm_eq p_eq).
  apply: (@orthogonal_free _ L).
  apply: (sub_pairwise_orthogonal _ _ (ind_irrs_orthogonal nKL)) => //.
  move => f /slAB; rewrite mem_undup mem_cat.
  by case/orP => /ind_irrs1_ker_sub/ind_irrs1_subset.
apply: (perm_eq_coherent p_eq) => //.
case: (exists_phi pAK nAK) => phi phiA phi1.
have sAl1 : {subset SS A <= l1}.
  move => f fA; rewrite !mem_filter /= (sAl f fA) andbT.
  apply/andP; split; last first.
    by apply: contra psi_nA => /eqP <-.
  apply: contra psi_nA => /eqP/(congr1 (cfAut conjC)).
  rewrite cfConjCK => <-.
  by have := (conjC_closed_SX fA); rewrite !inE /= => /andP [].
have conj_l1 : conjC_closed l1.
  move => f /=; rewrite !inE !mem_filter /= => /and3P [f_n_cpsi f_n_psi fl].
  move: (conj_l f fl); rewrite inE /= => /andP [-> ->].
  rewrite andbT andTb; apply/andP; split.
    apply: contra f_n_psi => /eqP/(congr1 (cfAut conjC)).
    by rewrite !cfConjCK => ->.
  apply: contra f_n_cpsi => /eqP/(congr1 (cfAut conjC)).
  by rewrite !cfConjCK => ->.
have xi1_cond: [&& phi \in l1, psi \in calS & psi \notin l1].
  rewrite (sAl1 _ phiA) (slS _ psi_l) !andTb.
  by rewrite !mem_filter /= eqxx andbF.
apply: (extend_coherent precoherentS _ xi1_cond); split.
- by rewrite !filter_uniq.
- by move => f; rewrite 2!mem_filter => /and3P [_ _] /slS.
- exact: conj_l1.
- apply: IH; rewrite ?filter_uniq //.
    rewrite /l1 -rem_filter ?filter_uniq // size_rem //.
    by rewrite -rem_filter // size_rem // size_l -pred_Sn leq_pred.
  by move => f; rewrite !mem_filter => /and3P [_ _] /slAB.
- case/ind_irrs1P: (slS _ psi_l) => r -> _.
  by rewrite phi1 cfInd1 // mulrAC mulfV ?neq0GiC // mul1r isNatC_irr1.
have: psi \in in_tuple (SS B).
  by move: (slAB _ psi_l); rewrite mem_undup mem_cat (negPf psi_nA) orFb.
move/tnthP => [j] ->; rewrite phi1.
have := ineq j => /=.
move/ltC_leC_trans; apply.
pose l2 := filter [predC (mem (SS A))] l1.
have peq_l1 : perm_eq l1 (SS A ++ l2).
  apply: uniq_perm_eq; rewrite ?filter_uniq //.
    rewrite cat_uniq !filter_uniq ?undup_uniq // andTb andbT.
    by apply/negP => /hasP [f]; rewrite mem_filter !inE /= => /andP [] /negPf ->.
  move => f; rewrite mem_cat.
  apply/idP/idP.
    case fA: (f \in SS A); rewrite (orTb, orFb) // => fl1.
    by rewrite mem_filter /= fl1 andbT fA.
  by case/orP => [/sAl1 |] //; rewrite mem_filter => /andP [].
rewrite (eq_big_perm _ peq_l1) big_cat /= -leC_sub addrAC subrr add0r.
rewrite big_seq; apply: posC_sum => f.
rewrite !mem_filter => /andP [_] /and3P [_ _] /slS/ind_irrs1_subset.
move/(ind_irrs_1Z nKL) => int_f1.
by rewrite -int_normCK // expr2 !posC_mul ?posC_norm // posC_inv cfnorm_posC.
Qed.



Lemma pf62 : (#|K : A|%:R - 1)^+2 <= 4%:R * #|L|%:R^+2 / #|C|%:R / #|D|%:R.
Proof.
have [psi psiB] : exists2 psi, psi \in SS B & 
  \sum_(f <- SS A) (f 1%g)^+2 / '[f]_L <= 2%:R * psi 1%g * #|L : K|%:R.
  have coherentSAB : coherent (undup (SS A ++ SS B)) L^# tau -> 
                     coherent (SS B) L^# tau.
    case => [tau1] [] isom to eq_tau.
    exists tau1; [split | ].
    - by move => f g /sZAB fZ /sZAB gZ; rewrite isom.
    - by move => f /sZAB/to.
    by move => f /sZAB/eq_tau.
  have : existsb i : ordinal (size (SS B)), 
    let psi := tnth (in_tuple (SS B)) i in
    ~~ (2%:R * psi 1%g * #|L : K|%:R < \sum_(f <- SS A) (f 1%g)^+2 / '[f]_L).
    rewrite -negb_forall.
    apply: contraT; rewrite negbK.
    move/ineq1_neg/(_ (undup (SS A ++ SS B))) => cond.
    case: not_coherentSB; apply: coherentSAB; apply: cond => //.
    - exact: undup_uniq.
    - move => f /=; rewrite !inE !mem_undup !mem_cat.
      by case/orP => /conjC_closed_SX; rewrite !inE => /andP [-> ->]; 
        rewrite (orTb, orbT).
    by move => f fS; rewrite mem_undup mem_cat fS orTb.
  case/existsP => i /=.
  set psi := tnth _ _.
  have psiB : psi \in SS B by rewrite /psi (tnth_nth 0) mem_nth ?ltn_ord.
  rewrite realC_neg_lt.
  - by exists psi.
  - rewrite /isRealC !rmorphM !rmorph_nat rmorph_IntC //.
    by apply: (ind_irrs_1Z nKL); move/ind_irrs1_ker_sub/ind_irrs1_subset: psiB.
  rewrite /isRealC rmorph_sum; apply/eqP.
  rewrite big_seq [in X in _ = X]big_seq; apply: eq_bigr => f fS.
  rewrite rmorphM fmorphV {1}cfdotC conjCK; congr (_ / _).
  rewrite expr2 rmorphM rmorph_IntC //.
  by apply: (ind_irrs_1Z nKL); move/ind_irrs1_ker_sub/ind_irrs1_subset: fS.
rewrite ind_irrs1_ker_sum1 // mulrC.
have indexLK : 0 < #|L : K|%:R by rewrite -(ltn_ltC 0) indexg_gt0.
rewrite leC_pmul2r //.
have pos_ineq: 0 <= #|K : A|%:R - 1.
  by rewrite leC_sub -(leq_leC 1) indexg_gt0.
move/(leC_square pos_ineq) => ineq.
apply/(leC_trans ineq).
rewrite exprn_mull expr2 -natr_mul -!mulrA.
rewrite leC_pmul2l -?(ltn_ltC 0) //.
case/ind_irrs1_kerP: psiB => r [-> _ sBker].
rewrite cfInd1 // exprn_mull -(LaGrange sKL) mulnC natr_mul.
rewrite -!mulrA leC_pmul2l // [in X in _ <= X]mulrC -!mulrA leC_pmul2l //.
rewrite !mulrA [in X in _ <= X]mulrC !mulrA -expr2.
apply: (irr1_bound_quo _ sBker) => //.
rewrite (normalS _ _ nBL) //; last by rewrite normal_sub.
exact: (subset_trans sBD).
Qed.


End PF62.

End PF61.

End Six.



