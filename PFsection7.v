(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup commutator nilpotent.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import frobenius inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection4 PFsection5.

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

(*
Lemma cfdotRes (S : {set gT}) (f g : 'CF(G)):
  f \in 'CF(G, S) -> '[f, g]_G = #|S|%:R / #|G|%:R * '['Res[S] f, 'Res[S] g].
Proof.
move => fGS.
rewrite (cfdotEl _ fGS) /cfdot.
rewrite mulrAC mulrA mulfV ?
Check cfdotE.
rewrite [in X in _ = X]cfdotE.
Check cfdotE.
move => supp_f; rewrite !inner_prodE; congr (_ * _).
apply: eq_bigr => x xG; rewrite !cfunE.
case: (boolP (x \in S)); first by rewrite mul1r.
by move => xnS; rewrite (supportP supp_f _ xnS) !mul0r.
Qed.
*)

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

(*
Lemma cfuni_conj x : x \in 'N(K) -> ('1_K ^ x)%CF = '1_K.
Proof. by move => xNK; apply/cfunP => g; rewrite !cfunE memJ_norm ?in_group. Qed.
*)

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
rewrite (big_rem _ _ _ one_in_ind_irrs) /= -ind_irrs1_rem.
rewrite cfnorm_Ind1 // cfInd1 ?normal_sub // cfun1E in_group.
rewrite mulr1 mulfV ?neq0GiC // expr2 mulr1.
by move/eqP; rewrite eq_sym addrC -subr_eq -mulr_subl => /eqP ->.
Qed.

End SumLemma.


(* Properties of chi \in Iirr L, chi \in induced_irrs1 *)

Variable r : Iirr L.
Hypothesis r_ind : 'chi_r \in induced_irrs1.
Hypothesis r1 : 'chi_r 1%g = e.

Lemma pre_beta_vchar : 'Ind[L, K] 1 - 'chi_r \in 'Z[irr L, K^#].
Proof.
rewrite vchar_split; apply/andP; split.
  by rewrite sub_vchar ?char_vchar ?cfInd_char ?irr_char ?cfun1_char.
rewrite cfun_onE; apply/subsetP => x; apply: contraR.
rewrite !inE cfInd_cfun1 // !cfunE negb_and negbK cfuniE //.
case/orP => [/eqP -> | xnK].
  by rewrite r1 in_group mulr1 subrr.
rewrite (supportP (support_ind_irrs1 r_ind) _ xnK).
by rewrite (negPf xnK) mulr0 subr0.
Qed.

Lemma pre_beta_memc : 'Ind[L, K] 1 - 'chi_r \in 'CF(L, K^#).
Proof. by rewrite cfun_onE (support_vchar pre_beta_vchar). Qed.

Lemma ind_irrs1_sub_e_vchar f : 
  f \in induced_irrs1 -> f - (f 1%g / e) *: 'chi_r \in 'Z[induced_irrs1, K^#].
Proof.
move => fS; rewrite vchar_split.
rewrite sub_vchar ?scale_vchar ?ind_irrs1_vcharW ?ind_irrs1_1eZ // andTb.
rewrite cfun_onE; apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK].
  by rewrite r1 -mulrA mulVf ?neq0GiC // mulr1 subrr.
by rewrite !(supportP (support_ind_irrs1 _) _ xnK) // mulr0 subr0.
Qed.

Lemma ind_irrs1_sub_e_memc f :
  f \in induced_irrs1 -> f - (f 1%g / e) *: 'chi_r \in 'CF(L, K^#).
Proof. 
by move => fS; rewrite cfun_onE (support_vchar (ind_irrs1_sub_e_vchar fS)).
Qed.

End InducedIrrs.



(********************************)
(* The proof of 5.9 *)
Section MoreFive.

Variable (gT : finGroupType) (G : {group gT}).
Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

Local Notation Atau := (Dade_support ddA).

Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.

Section PF59.

(* PF 5.9(b) *)
Lemma pf59b xi : xi \in irr L -> support xi \subset 1%g |: A ->
  exists t : Iirr G, (xi - (xi^*)%CF)^\tau = 'chi_t - (('chi_t)^*)%CF.
Proof.
move => xiIrr supp_xi.
case: (boolP (xi == (xi^*)%CF)) => [/eqP <- | xi_n_conj].
  by exists 0; rewrite chi0_1 cfConjC1 !subrr Dade0.
have A1 : A = (1%g |: A)^#.
  apply/eqP; rewrite eqEsubset subsetD1 subsetUr notA1 !andTb.
  by apply/subsetP => x; rewrite !inE => /andP [/negPf ->]; rewrite orFb.
have xiZ: xi \in 'Z[irr L] by case/irrP: xiIrr => i ->; exact: irr_vchar.
set f := _ - _.
have fZ : f \in 'Z[irr L, A].
  by rewrite A1 sub_vchar_cconj // vchar_split cfun_onE xiZ supp_xi.
have fC : f \in 'CF(L, A) by apply: (vchar_on fZ).
have tau_fZ : f^\tau \in 'Z[irr G, G^#].
  by rewrite vchar_split Dade_vchar ?fZ // andTb cfunD1E Dade1.
have norm_f_tau : '[f^\tau]_G = 2%:R.
  rewrite Dade_isometry // /f; move: xi_n_conj.
  case/irrP: xiIrr => r ->.
  case/irrP: (cfConjC_irr r) => t -> r_n_t.
  rewrite cfnorm_subd !cfdot_irr ?eqxx -?natr_add //.
  case rt: (r == t) => //.
  by move: r_n_t; rewrite (eqP rt) eqxx.
case: (vchar_norm2 tau_fZ norm_f_tau) => i; case => j [jni f_tau].
exists i; rewrite f_tau; congr (_ - _).
have: ((f^\tau)^*)%CF = - (f^\tau).
  rewrite (Dade_conjC ddA fC).
  suff ->: (f^*)%CF = -f by rewrite linearN.
  by apply/cfunP => x; rewrite !cfunE rmorph_sub conjCK oppr_sub.
rewrite f_tau oppr_sub.
have ->: (('chi_i - 'chi_j)^*)%CF = (('chi_i)^*)%CF - (('chi_j)^*)%CF.
  by apply/cfunP => x; rewrite !cfunE rmorph_sub.
move/esym/eqP; rewrite -!conjC_IirrE.
have := eq_irr_diff 1%N 1%N j i (conjC_Iirr i) (conjC_Iirr j).
rewrite !scale1r /=.
by move ->; rewrite (negPf jni) andFb orbF => /andP [/eqP ->].
Qed.


(**************************************)
(* PF 5.9(a) *)
Variable u : {rmorphism algC -> algC}.

Local Notation "alpha ^\u" := (cfAut u alpha)
  (at level 2, format "alpha ^\u").


(* Variables and assumptions of 5.9(a) *)

Variable calS : seq 'CF(L).
Variable tau1 : {additive 'CF(L) -> 'CF(G)}.
Variable chi : 'CF(L).

Hypothesis size_ge2 : size calS >= 2.
Hypothesis freeS : free calS.
Hypothesis sSirrL : {subset calS <= irr L}.
Hypothesis ZL_eq_ZA : 'Z[calS, L^#] =i 'Z[calS, A].
Hypothesis S_inv : {in calS, forall f, f^\u \in calS}.
Hypothesis tau1_to : {in 'Z[calS], forall f, tau1 f \in 'Z[irr G]}.
Hypothesis tau1_isom : {in 'Z[calS] &, isometry tau1}.
Hypothesis tau1_tau : {in 'Z[calS, A], forall f, tau1 f = f^\tau}.
Hypothesis chiS : chi \in calS.


Let sSZS : {subset calS <= 'Z[calS]}.
Proof. by move => f fS; rewrite mem_vchar. Qed.

Let sSZSL : {subset calS <= 'Z[calS, L]}.
Proof.
move => f fS; rewrite vchar_split sSZS // andTb.
case/irrP: (sSirrL fS) => r ->.
by rewrite cfun_onE support_cfun.
Qed.

Let val1scaleZ (f g : 'CF(L)) (S : seq 'CF(L)) K : 
  f \in calS -> g \in 'Z[S, K] -> f 1%g *: g \in 'Z[S, K].
Proof.
move => fS gZ.
case/irrP: (sSirrL fS) => r ->.
case/isNatCP: (char1_Nat (irr_char r)) => nn ->.
by rewrite scaler_nat; apply: muln_vchar.
Qed.

Let val1scale f g : f \in calS -> g \in calS -> f 1%g *: g \in 'Z[calS].
Proof. move => fS gS; apply: val1scaleZ => //; exact: sSZS. Qed.

Let diff_ZA (psi : 'CF(L)) : psi \in calS -> 
  psi 1%g *: chi - chi 1%g *: psi \in 'Z[calS, A].
Proof.
move => psiS; rewrite -ZL_eq_ZA.
rewrite vchar_split; apply/andP; split.
  by apply: sub_vchar; exact: val1scale.
rewrite cfun_onE; apply/subsetP => x; apply: contraR; rewrite inE negb_and in_set1 negbK.
case/orP => [/eqP -> | xnL]; rewrite !cfunE; first by rewrite mulrC subrr.
by rewrite !(supportP (support_vchar (sSZSL _)) _ xnL) // !mulr0 subrr.
Qed.

Let natr_psi1 psi : psi \in calS -> exists m, psi 1%g = m%:R.
Proof.
move => psiS; case/irrP: (sSirrL psiS) => r ->.
by apply/isNatCP; exact: isNatC_irr1.
Qed.


Let tau1_irr : exists eps : bool, forall psi, psi \in calS ->
  exists2 mu, mu \in irr G & tau1 psi = (-1) ^+ eps *: mu.
Proof.
have psi_norm : forall psi, psi \in calS -> '[tau1 psi]_G = 1%:R.
  move => psi psiS; rewrite (tau1_isom (sSZS psiS)) ?sSZS //.
  by case/irrP: (sSirrL psiS) => r ->; rewrite cfdot_irr eqxx.
case: (vchar_norm1P (tau1_to (sSZS chiS)) (psi_norm chi chiS)) => eps.
case => t zi_chi.
exists eps => psi psiS.
exists ((-1) ^+ eps *: tau1 psi); last by rewrite scalerA -expr2 sqr_sign scale1r.
set e := (-1) ^+ eps.
have e_cases: (e == 1) || (e == -1).
  by rewrite /e; case: {zi_chi e}eps; rewrite ?expr1 ?expr0 eqxx ?orbT ?orTb.
have posH: 0 < (e *: tau1 psi) 1%g.
  have: (psi 1%g *: tau1 chi - chi 1%g *: tau1 psi) 1%g = 0.
    move: (diff_ZA psiS).
    case: (natr_psi1 psiS) => a ->.
    case: (natr_psi1 chiS) => b ->.
    rewrite !scaler_nat => diff.
    by rewrite -!raddfMn -raddf_sub tau1_tau // Dade1.
  rewrite zi_chi -/e !cfunE.
  move/eqP; rewrite subr_eq0 mulrCA -signr_oppC -mulrCA.
  case/irrP: (sSirrL chiS) => i ->.
  case/irrP: (sSirrL psiS) => j ->.
  have chi1_n0 : 'chi_i 1%g != 0 by exact: irr1_neq0.
  rewrite -[_ * _]mul1r -(mulfV chi1_n0) -mulrA mulfV // => /eqP/(mulfI (chi1_n0)) eq.
  by rewrite -eq 3?sposC_mul ?ltC_irr1 ?spocC_inv // sposC_inv ltC_irr1.
have psi_irr := vchar_norm1P (tau1_to (sSZS psiS)) (psi_norm psi psiS).
case: psi_irr => ee [r] tau1_eq; move: posH; rewrite tau1_eq scalerA -signr_addb.
case: (_ (+) _); rewrite (expr1, expr0) ?scaleNr scale1r ?irr_chi //.
by rewrite cfunE sposC_opp => /ltC_geF; rewrite leC_eqVlt ltC_irr1 orbT.
Qed.


Lemma pf59a : (tau1 chi)^\u = tau1 (chi^\u).
Proof.
have sZACA: {subset 'Z[calS, A] <= 'CF(L, A)} by exact: vchar_on.
(* have sSCF : {subset calS <= 'CF(L)} by [] *)
have [psi psiS chi_n_psi]: exists2 psi, psi \in calS & chi != psi.
  pose S := rem chi calS.
  pose psi := S`_0.
  have: psi \in S.
    apply: mem_nth; rewrite size_rem //.
    rewrite -(ltn_add2l 1) !add1n prednK //.
    by apply: (ltn_trans _ size_ge2).
  rewrite /S rem_filter ?uniq_free // mem_filter /= eq_sym => /andP [chi_n_psi psiS].
  by exists psi.
have : psi 1%g *: (tau1 chi)^\u - chi 1%g *: (tau1 psi)^\u =
       psi 1%g *: tau1 (chi^\u) - chi 1%g *: tau1 (psi^\u).
  move: (diff_ZA psiS).
  case: (natr_psi1 psiS) => a ->; case: (natr_psi1 chiS) => b -> diff.
  transitivity ((a%:R *: chi - b%:R *: psi)^\tau)^\u.
    rewrite -tau1_tau ?diff // !scaler_nat raddf_sub !raddfMn /=.
    by rewrite rmorphD !rmorphMn rmorphN /=.
  rewrite Dade_auto ?sZACA // -tau1_tau ?vchar_auto //.
  by rewrite rmorph_sub !scaler_nat !rmorphMn /= raddf_sub !raddfMn.
case: (natr_psi1 psiS) => a a_psi1; rewrite a_psi1.
case: (natr_psi1 chiS) => b ->.
case: tau1_irr => eps; set e := _ ^+ _; move => psi_irr.
have: (tau1 chi)^\u != (tau1 psi)^\u.
  move: chi_n_psi; apply: contra.
  move/eqP/cfAut_inj/eqP; rewrite -subr_eq0 => /eqP diff0.
  rewrite -subr_eq0 -(cfnorm_eq0) -tau1_isom ?sub_vchar ?sSZS //.
  by rewrite raddf_sub diff0 cfdot0l.
case: (psi_irr _ (S_inv psiS)) => g2 g2_irr ->.
case: (psi_irr _ (S_inv chiS)) => f2 f2_irr ->.
case: (psi_irr _ psiS) => g1 g1_irr ->.
case: (psi_irr _ chiS) => f1 f1_irr ->.
have isZe : isIntC e by exact: isIntC_sign.
have e_n0: e != 0 by rewrite signr_eq0.
rewrite !cfAutZ_Int // scaler_sign_oppC scalerA -expr2 sqr_sign scale1r.
rewrite !scalerA mulrC [_ * e]mulrC -!scalerA -!scaler_subr => H1.
move/(scalerI e_n0) => /eqP; move: H1.
case/irrP: f2_irr => i ->; case/irrP: g2_irr => j ->.
case/irrP: f1_irr => r0 ->; case/irrP: g1_irr => t0 ->.
case/irrP: (cfAut_irr u r0) => r ->; case/irrP: (cfAut_irr u t0) => t ->.
rewrite eq_irr_diff; case rt: (r == t); first by rewrite (eqP rt) eqxx.
rewrite eqN_eqC -a_psi1; case/irrP: (sSirrL psiS) => s ->.
by rewrite (negPf (irr1_neq0 s)) !andFb orFb orbF => _ /andP [/eqP ->].
Qed.

End PF59.

End MoreFive.


(* The main section *)
Section Seven.

Variable (gT : finGroupType) (G : {group gT}).

(* PF 7.1 - 7.3 *)
Section PF71_73.

Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

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

Lemma rho_Dade_reciprocity chi alpha : alpha \in 'CF(L, A) ->
  '[alpha^\tau, chi]_G = '[alpha, chi^\rho]_L.
Proof.
move => alphaC.
apply: general_Dade_reciprocity => //.
by move => a aA /=; rewrite cfunElock aA.
Qed.

Lemma norm_chi_rho chi : '[chi^\rho]_L 
  = #|L|%:R ^-1 * (\sum_(a \in A) normC (chi^\rho a) ^+ 2).
Proof. by apply: cfnormE; rewrite cfun_onE; exact: support_rho. Qed.

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
Lemma pf73 chi : '[chi^\rho]_L <=
  #|G|%:R ^-1 * (\sum_(g \in Atau) normC (chi g) ^+ 2) ?= iff
    (forallb a, (a \in A) ==> 
      (forallb u, (u \in H a) ==> (chi (u * a)%g == chi a))).
Proof.
have chi1_proof : is_class_fun <<G>> [ffun g => if g \in Atau then chi g else 0].
  rewrite genGid; apply: intro_class_fun => [x y xG yG | x notGx]; last first.
    case xAtau: (_ \in _) => //.
    by move: (subsetP (Dade_support_sub ddA) x xAtau); rewrite (negPf notGx).
  have ->: (x ^ y \in Atau) = (x \in Atau).
    by apply/esym; rewrite -(memJ_conjg Atau y) Dade_supportJ.
  by case xAtau: (_ \in _) => //; rewrite cfunJ.
pose chi1 := Cfun 0 chi1_proof.
have <-: chi1^\rho = chi^\rho.
  apply/cfunP => a; rewrite !cfunElock.
  case aA: (_ \in _); last by [].
  congr (_ * _); apply: eq_bigr => x xHa; rewrite cfunE.
  suff ->: (x * a)%g \in Atau by [].
  apply/bigcupP; exists a; first by [].
  rewrite /Dade_support1 class_supportEr; apply/bigcupP.
  exists 1%g; rewrite ?in_group ?conjsg1 //.
  by apply/rcosetP; exists x.
set RHS := _ * _.
have <-: '[chi1]_G = RHS.
  have supp1: chi1 \in 'CF(G, Atau).
    rewrite cfun_onE.
    apply/subsetP => x; rewrite !inE /chi1 cfunE.
    by case: (_ \in _); [ | move/eqP; case].
  rewrite (cfnormE supp1) /RHS.
  congr (_ * _); apply: eq_bigr => x xAtau; congr (_ _ ^+ 2).
  by rewrite cfunE xAtau.
have := pf72b chi1.
set C1 := chi1 == _.
set C2 := (forallb a, _).
suff ->: C1 = C2 by [].
have xa: forall a x, a \in A -> x \in H a -> chi (x * a)%g = chi1 (x * a)%g.
  move => a x aA xHa; rewrite !cfunE.
  suff ->: (x * a)%g \in Atau by [].
  apply/bigcupP; exists a => //.
  rewrite /Dade_support1 class_supportEr; apply/bigcupP.
  exists 1%g; first by rewrite in_group.
  by rewrite conjsg1; apply/rcosetP; exists x.
apply/eqP/forallP.
  move => chi1_eq a.
  apply/implyP => aA; apply/forallP => x; apply/implyP => xHa; apply/eqP.
  rewrite -{2}[a]mul1g !xa ?in_group // mul1g chi1_eq.
  rewrite !(DadeE _ aA) // /Dade_support1 class_supportEr.
    apply /bigcupP; exists 1%g; first by rewrite in_group.
    by rewrite conjsg1; apply/rcosetP; exists 1%g; rewrite ?in_group ?mul1g.
  apply/bigcupP; exists 1%g; first by rewrite in_group.
  by rewrite conjsg1; apply/rcosetP; exists x.
move => hyp; apply/cfunP => g; rewrite cfunE.
case gAtau: (_ \in _); last first.
  symmetry; apply (supportP (support_Dade ddA chi1^\rho)).
  by rewrite gAtau.
case/bigcupP: gAtau => a aA.
rewrite /Dade_support1 class_supportEr.
case/bigcupP => x xG; case/imsetP => y.
case/rcosetP => u uHa -> -> {y}.
rewrite !cfunJ // (DadeE _ aA) => {x xG}; last first.
  rewrite /Dade_support1 class_supportEr; apply/bigcupP.
  exists 1%g; first by rewrite in_group.
  by rewrite conjsg1; apply/rcosetP; exists u.
rewrite /rho_fun cfunElock aA -[chi _]mul1r.
rewrite -{1}(@mulVf _ (#|H a|%:R)) -?mulrA ?neq0GC //.
congr (_ * _); rewrite -sum1_card natr_sum -mulr_suml mul1r.
apply: eq_bigr => x xHa; rewrite -xa //.
move/implyP: {hyp}(hyp a) => /(_ aA) /forallP => hyp.
by move: (hyp x) (hyp u)=> /implyP/(_ xHa)/eqP=> -> /implyP/(_ uHa)/eqP=> ->.
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


Local Notation G0 := (G :\: \bigcup_(i < m) 'Atau_i).


Section PartitionLemma.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Variables T I : finType.


Lemma partition_big_images (F : I -> {set T}) E :
  let P := [set (F i) | i <- I] in
    (forall i j, i != j -> [disjoint (F i) & (F j)]) ->
    \big[op/idx]_(x \in cover P) E x =
    \big[op/idx]_(i \in I) \big[op/idx]_(x \in F i) E x.
Proof.
move => P disjF.
have trivP: trivIset P.
  apply/trivIsetP => X Y.
  case/imsetP => i _ ->; case/imsetP => j _ -> neq.
  by apply: disjF; move: neq; apply: contra => /eqP ->.
rewrite big_trivIset //.
set f := fun i => \big[op/idx]_(x \in F i) E x.
have ->: \big[op/idx]_(i \in I) (f i) = \big[op/idx]_(i \in setT) (f i).
  by apply: eq_bigl => x; rewrite inE in_setT.
rewrite (partition_big_imset (fun i => F i)).
have ->: [set F i | i <- [set: I]] = P.
  rewrite -setP /P => x.
  by apply/imsetP/imsetP => [[] | []] y _ xFy; exists y.
apply: eq_bigr => S SP.
case: (boolP (S == set0)).
  move/eqP ->.
  rewrite !big1 //; last by move => i; rewrite in_set0.
  by move => i /andP [_ /eqP f0]; rewrite /f f0 big_set0.
move: SP; rewrite /P => /imsetP [j _ ->] Fjn0.
have ->: \big[op/idx]_(i \in [set: I] | F i == F j) (f i) = f j.
  apply: big_pred1 => i /=; rewrite in_setT andTb.
  apply/eqP/eqP; last by move ->.
  move/eqP => Feq; apply/eqP; move: Feq.
  apply: contraTT => ij.
  have := disjoint_setI0 (disjF i j ij).
  case: (boolP (F i == F j)); last by [].
  move/eqP ->; rewrite setIid => hyp; move: Fjn0.
  by rewrite hyp; move/eqP.
by rewrite /f; apply: eq_bigl => x.
Qed.


End PartitionLemma.
  


(* 7.5 *)
Lemma pf75 (r : Iirr G) : 
  #|G|%:R ^-1 * ((\sum_(g \in G0) normC ('chi_r g) ^+ 2) - #|G0|%:R)
    + \sum_(i < m) ('[('chi_r)^\rho_i]_(tnth L i)
                      - #|tnth A i|%:R / #|tnth L i|%:R) <= 0.
Proof.
set G0 := G :\: _.
rewrite mulr_addr.
set X := _ * (\sum_(g \in G0) _).
rewrite big_split /=.
set Y := \sum_(i < m) _.
pose f (j : Iirr G) i := #|G|%:R ^-1 * \sum_(g \in 'Atau_i) normC ('chi_j g) ^+ 2.
have F1: forall j, 
  1 = #|G|%:R^-1 * (\sum_(g \in G0) normC ('chi_j g) ^+ 2)
    + \sum_(i < m) f j i.
  move => j; rewrite /f.
  have {1}<-: '['chi_j]_G = 1 by rewrite cfdot_irr eqxx.
  rewrite mulr_sumr -mulr_addr cfdotE; congr (_ * _).
  have sG0G: G0 \subset G by exact: subsetDl.
  have DGG0: G :\: G0 = \bigcup_(i < m) 'Atau_i.
    rewrite setDDr setDv set0U.
    by apply/setIidPr; apply/bigcupsP => i _; exact: Dade_support_sub.
  rewrite (big_setID G0) /= (setIidPr sG0G) DGG0.
  congr (_ + _); first by apply: eq_bigr => g _; rewrite sqrtCK.
  pose F i := 'Atau_i.
  have ->: \bigcup_(i0 < m) 'Atau_i0 = cover [set F i | i <- 'I_m].
    rewrite /cover -setP => x.
    apply/bigcupP/bigcupP => [[] | []].
      move => i _ xA.
      by exists 'Atau_i => //; apply/imsetP; exists i.
    by move => S; case/imsetP => i _ -> xF; exists i.
  rewrite partition_big_images /=; last by exact: disjointA.
  by apply: eq_bigr => i _; apply: eq_bigr => x _; rewrite sqrtCK.
have: Y <= \sum_(i < m) f r i.
  rewrite -leC_sub -sumr_sub.
  apply: posC_sum => i _; rewrite leC_sub.
  by apply: pf73; exact: memc_irr.
have: \sum_(i < m) f 0 i = \sum_(i < m) #|tnth A i|%:R / #|tnth L i|%:R.
  apply: eq_bigr => i _.
  have := pf73 (ddI i) 1.
  set cond := forallb a, _.
  have auG: forall a u, a \in tnth A i -> u \in tnth H i a -> a \in G /\ u \in G.
    move => a u aA uH; split.
      have: tnth A i \subset tnth L i by  have [/subsetD1P[]] := ddI i.
      move/subsetP => /(_ a aA); apply: (subsetP _).
      by have [_ /subsetIP[]] := ddI i.
    move: uH; apply: (subsetP _).
    have [_ _ _ /(_ a aA) /sdprod_context []] := ddI i.
    by move/andP; rewrite subsetI => [] [] /andP [].
  have: cond.
    apply/forallP => {cond}x; apply/implyP => xA.
    apply/forallP => u; apply/implyP => uH.
    move: (auG x u xA uH) => [xG uG].
    by rewrite !cfun1E groupM ?xG.
  move => C /leCifP.
  rewrite C {C} /(f 0) chi0_1 => /eqP <-.
  rewrite (norm_chi_rho (ddI i)) mulrC; congr (_ * _).
  rewrite -sum1_card natr_sum; apply: eq_bigr => g gA.
  have <-: normC (1%:R) ^+ 2 = 1%:R by rewrite normC1 exp1rn.
  congr (_ _ ^+ 2).
  rewrite rho_1 cfuniE ?gA // /normal.
  by case: (ddI i) => /subsetD1P [] -> _ /subsetIP [] _ ->.
move => h1 h2.
rewrite sumr_opp -h1.
rewrite -addrA [_ + (Y - _)]addrA [_ + Y]addrC -!addrA.
rewrite mulrN -mulN1r -[- \sum_(i < m) _]mulN1r -mulr_addr.
set S := #|G|%:R^-1 * #|G0|%:R + _.
have ->: S = 1.
  rewrite (F1 0); congr (_ + _); congr (_ * _).
  rewrite -sum1_card natr_sum; apply: eq_bigr => g gG0.
  rewrite chi0_1 (cfnorm_lin_char (cfun1_lin_char _)) ?expr2 ?mul1r //.
  by apply: subsetP gG0; exact: subsetDl.
rewrite addrA mulr1 -(subrr 1) leC_add2r.
by rewrite (F1 r) -/X leC_add2l h2.
Qed.

End PF74_75.


(* Hypothesis 7.6 and the proofs of 7.7 and 7.8 *)
Section PF76_78.

(* In this section, A = K^# with K <| L *)
Variables (K L : {group gT}) (H : gT -> {group gT}).
Let zi := induced_irrs K L.
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
Proof. by rewrite -mulrA mulVf ?(ind_irrs_1neq0 nKL) ?mulr1. Qed.

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
Lemma pf77a x : x \in A ->
  (chi^\rho) x = 
  \sum_(f <- zi) (c f)^* / '[f]_L * f x.
Proof.
move/andP: (nKL) => [_] sLNK xA.
pose psi (f : 'CF(L)) := f - d f *: zi0.
have psiC f: f \in zi -> psi f \in 'CF(L, A).
  move => f_zi; rewrite cfun_onE.
  apply/subsetP => g; rewrite inE /=; apply: contraR.
  rewrite inE negb_and negbK in_set1 !cfunE.
  case/orP => [| gnK]; first by move/eqP ->; rewrite zi_val1 subrr.
  suff [-> ->]: f g = 0 /\ zi0 g = 0 by rewrite mulr0 subrr.
  by split; apply: (supportP _ _ gnK); rewrite -cfun_onE memc_ind_irrs.
have f_eq f: f \in 'CF(L, A) -> f = e^-1 *: 'Ind[L, K] ('Res[K] f).
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
  have: exists j : 'I_n, 'Ind[L, K] 'chi_r = zi`_j.
    have: 'Ind[L, K] 'chi_r \in zi by apply/ind_irrsP; exists r.
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
    by rewrite cfunE -mulrA mulfV ?mulr1 // (ind_irrs_1neq0 nKL _) ?in_zi.
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
  move/eqP; rewrite mulf_eq0; move: (ind_irrs_1neq0 nKL zi0_in_zi).
  by case: (zi0 _ == 0); first by []; rewrite orbF => _ /eqP.
have {f_in_psi}f_eq0 f: f \in 'CF(L, A) ->
  (forall g, g \in zi -> '[psi g, f]_L = 0) -> f = 0.
  move => fC prod0; have := f_in_psi f fC; case => f_ f_sum.
  apply/eqP; rewrite -cfnorm_eq0.
  rewrite {2}f_sum raddf_sum big1 //= => i _.
  by rewrite cfdotZr cfdotC prod0 ?in_zi // conjC0 mulr0.
pose b (f : 'CF(L)) := (c f)^* / '[f]_L.
have b0 : b zi0 = 0.
  by rewrite /b/c/d mulfV ?(ind_irrs_1neq0 nKL _) //
    scale1r subrr Dade0 cfdot0l conjC0 mul0r.
pose f := chi^\rho - \sum_(g <- zi) b g *: g.
have fC : f \in 'CF(L, K).
  apply: memv_sub; last first.
    rewrite big_seq_cond; apply: memv_suml => g /andP [g_zi _].
    by apply: memvZl; exact: memc_ind_irrs.
  by apply: cfun_onS (rho_cfunS ddA _); exact: subD1set.
case: (crestr1 K f) => h [] hC /(_ x xA) f_eq_h h_inner; move: f_eq_h.
suff ->: h = 0.
  rewrite !cfunE => /eqP; rewrite addr_eq0 opprK => /eqP ->.
  by rewrite sum_cfunE; apply: eq_bigr => i _; rewrite cfunE.
apply: (f_eq0 _ (hC fC)) => g g_zi.
rewrite -h_inner ?psiC // cfdot_subr.
have ->: '[psi g, chi^\rho]_L = c g.
  by rewrite -rho_Dade_reciprocity // psiC.
rewrite cfdotDl cfdotNl !cfdot_sumr.
rewrite (bigID (pred1 g)) /= big_pred1_uniq ?uniq_ind_irrs // !big1_seq ?addr0.
- rewrite /b cfdotZr rmorphM fmorphV {1}cfdotC !conjCK subr0.
  by rewrite divfK (subrr, ind_irrs_norm_neq0 nKL).
- move => ff /andP [_ ff_zi]; rewrite cfdotZr cfdotZl.
  case ff_e_zi0: (ff == zi0).
    by rewrite (eqP ff_e_zi0) b0 conjC0 mul0r.
  by rewrite (ind_irrs_ortho nKL) ?mulr0 ?oppr0 // eq_sym ff_e_zi0.
move => ff /andP [ff_n_g ff_zi]; rewrite cfdotZr.
by rewrite (ind_irrs_ortho nKL) ?mulr0 // eq_sym.
Qed.


Lemma mulr_sum (I J : finType) (f : I -> algC) (g : J -> algC) :
  (\sum_(i \in I) f i) * (\sum_(j \in J) g j) = 
  \sum_(i \in I) \sum_(j \in J) f i * g j.
Proof.
elim/big_rec2: _; first by rewrite mul0r.
by move => i y1 y2 _ <-; rewrite mulr_addl mulr_sumr.
Qed.


Lemma pf77b : '[chi^\rho]_L = 
  \sum_(f <- zi) \sum_(g <- zi) ((c f)^* * c g / '[f]_L / '[g]_L
    * ('[f, g]_L - f 1%g * g 1%g / (e * k))).
Proof.
rewrite (cfnormE (rho_cfunS ddA _)) -ke.
have ->: \sum_(x \in A) `|chi^\rho x| ^+ 2 =
  \sum_(x \in A) (\sum_(i < n) \sum_(j < n) (c zi`_i)^* * (c zi`_j) / 
    '[zi`_i, zi`_i]_L / '[zi`_j, zi`_j]_L * (zi`_i x * (zi`_j x)^*)).
  apply: eq_bigr => x xA; rewrite (pf77a xA) (big_nth 0) big_mkord.
  rewrite normCK rmorph_sum mulr_sum.
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
rewrite (cfdotEl _ (memc_ind_irrs nKL (in_zi i))) -ke.
rewrite mulrA mulfV // mul1r.
rewrite (big_setID 1%g) /= setIg1 big_set1 -/X /Y.
congr (_ * _ + _).
rewrite posC_conjK //; apply: (@char1_pos _ L _).
case/ind_irrsP: (in_zi j) => r ->.
by apply: cfInd_char; rewrite ?sKL ?irr_char.
Qed.


End PF77.


(*************************)

(* 7.8 *)

Section PF78.

Variable nu : {additive 'CF(L) -> 'CF(G)}.
(* This corresponds to zi \in Iirr L, zi \in calS *)
Variable r : Iirr L.

Local Notation calS := (induced_irrs1 K L).
Local Notation beta := ('Ind[L, K] 1 - 'chi_r)^\tau.

Hypothesis chiS : 'chi_r \in calS.
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
Proof.
apply: contraR; rewrite negbK => zi_eq.
have := nth_uniq 0 (ltn_ord i) (ltn_ord j) (uniq_ind_irrs K L).
rewrite zi_eq => /eqP; rewrite eq_sym => /eqP /eqP h1.
by apply/eqP; exact: ord_inj.
Qed.

(* The consequence of coherence and that A = K^# *)
Let sizeS : size calS >= 2.
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
have : g \in calS by rewrite S inE eqxx orTb.
by move/ind_irrs1_subset/(ind_irrs_1neq0 nKL)/negPf ->.
Qed.

Lemma raddfMZ z f : isIntC z -> nu (z *: f) = z *: nu f.
Proof.
rewrite isIntCE; case/orP; case/isNatCP => m.
  by move ->; rewrite !scaler_nat raddfMn.
move/eqP; rewrite eqr_oppC => /eqP ->.
by rewrite !scaleNr !scaler_nat raddfMNn.
Qed.


Lemma pf78a1 f : f \in calS -> '[nu f, 1]_G = 0.
Proof.
move => fS.
have eq_g g : g \in calS -> '[nu (g - (g 1%g / e) *: 'chi_r), 1]_G = 0.
  move => gS; rewrite nu_tau; last by exact: ind_irrs1_sub_e_vchar.
  rewrite rho_Dade_reciprocity ?(cfuni_xi0, memc_irr) ?ind_irrs1_sub_e_memc //.
  rewrite rho_1.
  set mu := _ - _.
  have ->: '[mu, '1_A]_L = '[mu, 1]_L.
    rewrite !(cfdotEl _ (ind_irrs1_sub_e_memc nKL chiS chi1 gS)).
    congr (_ * _); apply: eq_bigr => x xK1.
    move: (xK1); rewrite inE => /andP [_] xK.
    by rewrite cfuniE ?xK1 ?cfun1E ?(subsetP sKL) // /normal sAL nAL.
  by rewrite cfdot_subl cfdotZl !(ind_irrs1_ortho1 nKL) // mulr0 subr0.
suff {f fS}: '[nu 'chi_r, 1]_G = 0.
  move => eq0; have := eq_g f fS.
  rewrite raddf_sub (raddfMZ _ (ind_irrs1_1eZ _ fS)) //.
  by rewrite cfdot_subl cfdotZl eq0 mulr0 subr0.
have norm_chi1 : '[nu 'chi_r, nu 'chi_r]_G = 1.
  by rewrite nu_isom ?cfdot_irr ?eqxx ?ind_irrs1_vcharW.
have chi_irr := vchar_norm1P (nu_to (ind_irrs1_vcharW nKL chiS)) norm_chi1.
case: chi_irr => e0 [] rr; set eps := _ ^+ _; move => chi_eq.
rewrite chi_eq cfdotZl.
case r0: (rr == 0); last first.
  by rewrite -chi0_1 cfdot_irr r0 mulr0.
have [f fS chi_n_f]: exists2 f, f \in calS & 'chi_r != f.
  pose S := filter (predC1 'chi_r) calS.
  suff: S`_0 \in S by rewrite mem_filter /= eq_sym => /andP [chi_n_f fS]; exists S`_0.
  rewrite /S -rem_filter ?uniq_ind_irrs1 //.
  apply: mem_nth; rewrite size_rem // -(ltn_add2l 1) !add1n prednK //.
  by apply: (ltn_trans _ sizeS).
have prod0 : '[nu f, 1]_G = 0.
  move/eqP: chi_eq; rewrite scaler_sign_oppC -chi0_1 (eqP r0) => /eqP <-.
  apply/eqP; rewrite cfdotZr mulf_eq0; apply/orP; right; apply/eqP.
  by rewrite nu_isom ?ind_irrs1_vcharW // (ind_irrs1_ortho nKL) // eq_sym.
have := eq_g f fS.
rewrite raddf_sub (raddfMZ _ (ind_irrs1_1eZ _ fS)) //.
rewrite cfdot_subl chi_eq !cfdotZl prod0 mulrA.
move/eqP; rewrite subr_eq eq_sym add0r mulf_eq0.
case/orP; last by move/eqP ->; rewrite mulr0.
rewrite mulrC -signr_oppC mulr0 mulf_eq0 invr_eq0 (negPf unit_e).
by rewrite (negPf (ind_irrs_1neq0 nKL _)) ?ind_irrs1_subset.
Qed.


(* 7.8(a)-2 *)

Lemma dot_beta_1 : '[beta, 1]_G = 1.
rewrite rho_Dade_reciprocity ?pre_beta_memc // rho_1.
set mu := _ - _.
have ->: '[mu, '1_A]_L = '[mu, 1]_L.
  rewrite !(cfdotEl _ (vchar_on (pre_beta_vchar _ _ _))) //.
  congr (_ * _); apply: eq_bigr => x xK1.
  move: (xK1); rewrite inE => /andP [_] xK.
  by rewrite cfuniE ?xK1 ?cfun1E ?(subsetP sKL) // /normal sAL nAL.
rewrite cfdot_subl -Frobenius_reciprocity (ind_irrs1_ortho1 nKL) // subr0.
by rewrite cfRes_cfun1 // cfnorm1.
Qed.

Lemma pf78a2 : exists a, exists Gamma,
  [/\ isIntC a, 
    '[Gamma, 1]_G = 0, 
    {in calS, forall f, '[Gamma, nu f]_G = 0} &
    beta = Gamma + 1 - nu 'chi_r + 
           a *: (\sum_(f <- calS) (f 1%g / e / '[f]_L) *: nu f)].
Proof.
exists ('[beta, nu 'chi_r]_G + 1).
exists (beta - '[beta, 1]_G *: 1 - 
  \sum_(f <- calS) ('[beta, nu f]_G / '[f]_L) *: nu f).
split.
- have ->: (1 : algC) = 1%:R by [].
  apply: isIntC_add; last by exact: isIntC_nat.
  apply: cfdot_vchar_Int; last by apply: nu_to; exact: ind_irrs1_vcharW.
  by apply: Dade_vchar; exact: pre_beta_vchar.
- rewrite !cfdotDl !cfdotNl cfdotZl.
  rewrite cfnorm1 mulr1 subrr.
  apply/eqP; rewrite subr_eq0 eq_sym; apply/eqP.
  rewrite cfdot_suml big1_seq //.
  move => f /andP [_] fS.
  by rewrite cfdotZl (pf78a1 fS) mulr0.
- move => f fS /=.
  rewrite !cfdotDl !cfdotNl cfdotZl.
  rewrite ['[1, _]_G]cfdotC (pf78a1 fS) conjC0 mulr0 subr0.
  apply/eqP; rewrite subr_eq0 eq_sym; apply/eqP; rewrite cfdot_suml.
  rewrite (bigID (pred1 f)) /= big_pred1_uniq ?uniq_ind_irrs1 // big1_seq; last first.
    move => g /andP [gnf gS]; move: gnf.
    rewrite cfdotZl nu_isom ?(ind_irrs1_vcharW nKL) // => gnf.
    by rewrite (ind_irrs1_ortho _ gS fS gnf) // mulr0.
  rewrite addr0 cfdotZl nu_isom ?ind_irrs1_vcharW //.
  by rewrite divfK // (ind_irrs_norm_neq0 nKL) ?ind_irrs1_subset.
set SG := \sum_(_ <- _) _.
set S := (_ + _) *: _.
rewrite dot_beta_1 scale1r [_ - _ - _]addrAC.
rewrite -[_ - 1 + _]addrA [- _ + _]addrC subrr addr0.
rewrite -!addrA -{1}[beta]addr0; congr (_ + _).
rewrite addrC; apply/eqP; rewrite eq_sym subr_eq0 eq_sym; apply/eqP.
rewrite /S /SG (bigID (pred1 'chi_r)) /=.
rewrite [in X in _ = X](bigID (pred1 'chi_r)) /=.
rewrite scaler_addr addrA; congr (_ + _).
  rewrite !big_pred1_uniq ?uniq_ind_irrs1 //.
  rewrite chi1 (mulfV unit_e).
  rewrite cfdot_irr eqxx invr1 mul1r scale1r scaler_addl.
  by rewrite mulr1 scale1r -addrCA [- _ + _]addrC subrr addr0.
rewrite scaler_sumr big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP [fS f_n_chi].
rewrite scalerA !mulrA; congr ((_ / _) *: _).
have: '[beta, nu (f - f 1%g / e *: 'chi_r)]_G = f 1%g / e.
  set c := _ / _.
  rewrite nu_tau ?ind_irrs1_sub_e_vchar //.
  rewrite Dade_isometry ?ind_irrs1_sub_e_memc ?pre_beta_memc //.
  rewrite !cfdot_subl !cfdot_subr !cfdotZr.
  rewrite cfdotC ind_irrs1_ortho_ind1 // conjC0 sub0r.
  rewrite (ind_irrs1_ortho _ chiS fS) //; last by rewrite eq_sym.
  rewrite cfdotC ind_irrs1_ortho_ind1 // conjC0 mulr0 oppr0 !add0r opprK.
  by rewrite cfdot_irr eqxx mulr1 isIntC_conj ?ind_irrs1_1eZ.
rewrite [nu _]raddf_sub raddfMZ ?ind_irrs1_1eZ // cfdot_subr.
move/eqP; rewrite subr_eq => /eqP ->.
rewrite -mulrA mulr_addl mul1r addrC cfdotZr mulrC.
by congr (_ * _ + _); apply: isIntC_conj; exact: ind_irrs1_1eZ.
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
have k_gt0: 0 < k by rewrite /k -(ltn_ltC 0) cardG_gt0.
have e_gt0: 0 < e by rewrite /e -(ltn_ltC 0) indexg_gt0.
have u_ge0: 0 <= u.
  rewrite -(posC_mulr _ e_gt0) mulrA mulfV // mul1r.
  rewrite -(posC_mulr _ k_gt0) mulr_subr mulfV // mulr1 leC_sub.
  by rewrite -(leq_leC 1) cardG_gt0.
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


Lemma pf78b1  : w <= '[(nu 'chi_r)^\rho]_L.
Proof.
pose a := '[beta, nu 'chi_r]_G + 1.
have aZ: isIntC a.
  rewrite isIntC_add ?(isIntC_nat 1) ?cfdot_vchar_Int ?nu_to ?ind_irrs1_vcharW //.
  by rewrite Dade_vchar ?pre_beta_vchar.
pose z0 := (filter (predC1 'chi_r) calS)`_0.
pose c (f : 'CF(L)) := '[(f - f 1%g / z0 1%g *: z0)^\tau, nu 'chi_r]_G.
have z0_in : z0 \in filter (predC1 'chi_r) calS.
  rewrite /z0 -rem_filter ?uniq_ind_irrs1 //.
  by apply: mem_nth; rewrite size_rem // -(subnK sizeS) addn2.
have z0S : z0 \in calS by move: z0_in; rewrite mem_filter => /andP [].
have z0_n_chi : z0 != 'chi_r by move: z0_in; rewrite mem_filter => /andP [] /=.
have z01_neq0 : z0 1%g != 0 by rewrite (ind_irrs_1neq0 nKL) ?ind_irrs1_subset.
have c0 : c z0 = 0 by rewrite /c mulfV // scale1r subrr Dade0 cfdot0l.
have c1 : c ('Ind[L, K] 1) = a.
  transitivity ('[beta + ('chi_r - 'Ind[L, K] 1 1%g / z0 1%g *: z0)^\tau, nu 'chi_r]_G).
    congr ('[_, _]_G); rewrite -linearD.
    by rewrite addrA -[_ - _ + _]addrA [- _ + _]addrC subrr addr0.
  apply: (mulfI z01_neq0).
  rewrite cfdotDl !mulr_addr; congr (_ + _).
  rewrite -cfdotZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
  rewrite /= -nu_tau ?nu_isom //
    ?cfInd_cfun1 ?cfunE ?cfuniE ?in_group ?mulr1 -/e -?chi1 //; first last.
  - exact: ind_irrs1_sub_vchar.
  - exact: ind_irrs1_vcharW.
  - by apply: (@vcharW _ _ _ A); exact: ind_irrs1_sub_vchar.
  rewrite cfdot_subl !cfdotZl cfdot_irr eqxx.
  by rewrite (ind_irrs1_ortho nKL) ?mulr1 ?mulr0 ?subr0.
have c2 : c 'chi_r = 1.
  apply: (mulfI z01_neq0).
  rewrite /c -cfdotZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
  rewrite /= -nu_tau ?nu_isom ?['chi_r \in _]ind_irrs1_vcharW //
    ?(@vcharW _ _ _ A) ?ind_irrs1_sub_vchar //.
  rewrite cfdot_subl !cfdotZl cfdot_irr eqxx.
  by rewrite (ind_irrs1_ortho nKL) ?mulr0 ?mulr1 ?subr0.
have ci0 f : f \in zi -> f != 'Ind[L, K] 1 -> f != 'chi_r -> c f = 0.
  move => f_zi f_n_1 f_n_chi.
  have fS: f \in calS by rewrite mem_filter /= f_zi f_n_1.
  apply: (mulfI z01_neq0).
  rewrite /c -cfdotZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
  rewrite /= -nu_tau ?nu_isom ?['chi_r \in _]ind_irrs1_vcharW //
    ?(@vcharW _ _ _ A) ?ind_irrs1_sub_vchar //.
  rewrite cfdot_subl !cfdotZl.
  by rewrite !(ind_irrs1_ortho nKL) ?mulr0 ?subr0.
rewrite (pf77b (ind_irrs1_subset z0S)).
pose pred12 := predU (pred1 ('Ind[L, K] 1)) (pred1 'chi_r).
rewrite (bigID pred12) /= addrC big1_seq ?add0r; last first.
  move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  apply: big1_seq => g /andP [_ g_zi].
  by move: (ci0 f f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite conjC0 !mul0r.
have sumU F f1 f2: f1 \in zi -> f2 \in zi -> f1 != f2 ->
     \sum_(i <- zi | (i == f1) || (i == f2)) (F i : algC) = F f1 + F f2.
  move => f1_zi f2_zi f1_n_f2; rewrite (bigID (pred1 f1)) /=.
  set S := \sum_(i <- zi | _) _; have {S}->: S = \sum_(i <- zi | i == f1) F i.
    by apply: eq_bigl => x; case: (_ == _) => //; rewrite andbF.
  rewrite big_pred1_uniq ?uniq_ind_irrs //.
  set S := \sum_(i <- zi | _) _; have {S}->: S = \sum_(i <- zi | i == f2) F i.
    apply: eq_bigl => x; case xf1: (_ == _) => /=; last by rewrite andbT.
    by move/eqP: xf1 ->; move/negPf: f1_n_f2 ->.
  by rewrite big_pred1_uniq ?uniq_ind_irrs.
have one_n_chi: 'Ind[L, K] 1 != 'chi_r.
  by case/ind_irrs1P: chiS => t ->; rewrite eq_sym.
rewrite sumU // ?one_in_ind_irrs ?ind_irrs1_subset //.
rewrite (bigID pred12) [in X in _ + X](bigID pred12) !sumU ?one_in_ind_irrs ?ind_irrs1_subset //=.
rewrite !big1_seq; first last.
- move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  by move: (ci0 f f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite mulr0 !mul0r.
- move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  by move: (ci0 f f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite mulr0 !mul0r.
move: c1 c2; rewrite /c => -> ->; rewrite -/a.
rewrite cfdot_irr eqxx cfnorm_Ind1 // cfInd1 // -/e.
rewrite cfun1E in_group !mulr1.
rewrite cfdotC ind_irrs1_ortho_ind1 // conjC0 conjC1.
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
rewrite (ortho_GammaS chiS) cfdotC (pf78a1 chiS).
rewrite conjC0 !add0r nu_isom ?ind_irrs1_vcharW // cfdot_irr eqxx addrC.
congr (_ - _); rewrite cfdot_suml.
rewrite (bigID (pred1 'chi_r)) /= big_pred1_uniq ?uniq_ind_irrs1 // big1_seq.
  rewrite cfdotZl chi1 (mulfV unit_e) cfdot_irr eqxx invr1.
  by rewrite nu_isom ?ind_irrs1_vcharW // cfdot_irr eqxx addr0 !mulr1.
move => f /andP [f_n_chi fS]; rewrite cfdotZl.
by rewrite nu_isom ?ind_irrs1_vcharW // (ind_irrs1_ortho nKL _ _ f_n_chi) ?mulr0.
Qed.

Let isIntC_a : isIntC a.
Proof.
move/eqP: a_eq; rewrite eq_sym subr_eq => /eqP ->.
rewrite isIntC_add ?(isIntC_nat 1) ?cfdot_vchar_Int ?nu_to ?ind_irrs1_vcharW //.
by rewrite Dade_vchar ?pre_beta_vchar.
Qed.


Lemma pf78b2 : '[Gamma]_G <= e - 1.
Proof.
have : '[beta]_G = e + 1.
  rewrite Dade_isometry ?pre_beta_memc //.
  rewrite cfdotDl !cfdotDr !cfdotNl !cfdotNr.
  rewrite cfnorm_Ind1 // cfdotC ind_irrs1_ortho_ind1 // conjC0.
  by rewrite cfdot_irr eqxx oppr0 sub0r addr0 -mulNrn mulr1n opprK.
rewrite beta_sum.
rewrite (bigID (pred1 'chi_r)) /= big_pred1_uniq ?uniq_ind_irrs1 // -big_filter.
rewrite chi1 mulfV // cfdot_irr eqxx invr1 mulr1 scale1r scaler_addr addrA.
set v1 := _ + 1 + _ + _.
set v2 := a *: _.
rewrite cfnormD.
have ->: '[v1, v2]_G = 0.
  rewrite cfdotZr cfdot_sumr big1_seq ?mulr0 //.
  move => f; rewrite mem_filter andTb => /andP [] f_n_chi fS.
  rewrite /= cfdotZr !cfdotDl cfdotZl cfdotNl.
  rewrite ortho_GammaS // nu_isom ?ind_irrs1_vcharW //.
  apply/eqP; rewrite mulf_eq0; apply/orP; right.
  rewrite cfdotC pf78a1 // cfdotC (ind_irrs1_ortho nKL) //.
  by rewrite conjC0 mulr0 !addr0 subr0.
rewrite conjC0 !addr0.
have ->: '[v1]_G = '[Gamma]_G + 1 + (a - 1) ^+ 2.
  rewrite /v1 -!addrA cfnormD.
  set x := '[Gamma, 1 + _]_G; have {x}->: x = 0.
    rewrite /x !cfdotDr !cfdotNr cfdotZr ortho_Gamma1.
    by rewrite ortho_GammaS // mulr0 addr0 subr0.
  rewrite -scaleN1r -scaler_addl cfnormD cfnorm1.
  set x := '[1, _]_G; have {x}->: x = 0.
    by rewrite /x cfdotZr cfdotC pf78a1 // conjC0 mulr0.
  rewrite conjC0 !addr0; congr (_ + (_ + _)).
  rewrite cfnormZ int_normCK ?isIntC_add ?isIntC_opp ?(isIntC_nat 1) // addrC.
  by rewrite nu_isom ?ind_irrs1_vcharW // cfdot_irr eqxx mulr1.
suff ->: '[v2]_G = a ^+ 2 * (k * u - 1).
  rewrite expr2 !mulr_subr !mulr_subl !mulr1 !mul1r -expr2.
  rewrite addrAC !addrA subrK mulrCA oppr_add opprK => /eqP.
  rewrite eq_sym -!addrA -subr_eq oppr_add !addrA addrK => /eqP <-.
  rewrite [_ + 1]addrC oppr_add addrA -{2}[e - 1]addr0 leC_add2l -posC_opp opprK.
  rewrite -addrA -mulr2n -mulr_natl mulrN -[_ * a]mul1r -{1}(mulfV unit_k).
  rewrite -!mulrA -mulr_subr -/v posC_mul ?posC_nat //.
  by rewrite mulrA -expr2 mulrC [v * _]mulrCA mulrA ineq1.
rewrite cfdotZl cfdotZr (isIntC_conj isIntC_a) expr2 mulrA; congr (_ * _).
have norm_sum (s : seq 'CF(L)) (F : 'CF(L) -> 'CF(G)) :
  uniq s -> {in s &, forall f g, f != g -> '[F f, F g]_G = 0} ->
  '[\sum_(f <- s) F f, \sum_(f <- s) F f]_G = \sum_(f <- s) '[F f, F f]_G.
  move => uniq_s ortho_s.
  rewrite raddf_sum big_seq_cond [in X in _ = X]big_seq_cond /=.
  apply: eq_bigr => f /andP [] fS _.
  rewrite (bigID (pred1 f)) /= big_pred1_uniq //.
  rewrite cfdotDl -{2}['[_, _]_G]addr0; congr (_ + _).
  rewrite cfdot_suml big1_seq //=.
  by move => g /andP [] gS g_n_f; rewrite ortho_s.
rewrite norm_sum ?filter_uniq ?uniq_ind_irrs //; last first.
  move => f g; rewrite mem_filter => /andP [_] fS.
  rewrite mem_filter => /andP [_] gS f_n_g.
  rewrite cfdotZl cfdotZr nu_isom ?ind_irrs1_vcharW //.
  by rewrite (ind_irrs1_ortho nKL fS gS f_n_g) !mulr0.
rewrite /u mulrCA mulr_subr mulfV // mulr1 mulrC -ind_irrs1_sum1 //.
apply/esym; rewrite (bigID (pred1 'chi_r)) /= big_pred1_uniq ?uniq_ind_irrs1 //.
rewrite chi1 mulfV // cfdot_irr eqxx invr1 expr2 !mulr1.
rewrite addrAC subrr add0r big_filter big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP [fS f_n_chi].
rewrite cfnormZ nu_isom ?ind_irrs1_vcharW // normC_mul !exprn_mull.
rewrite normC_inv !expr_inv int_normCK ?ind_irrs1_1eZ // exprn_mull expr_inv.
rewrite normCK -cfdotC; set x := '[f]_L; rewrite [(x * x)^-1]invf_mul.
by rewrite -!mulrA mulVf ?(ind_irrs_norm_neq0 nKL) ?ind_irrs1_subset // mulr1.
Qed.



(***************************************)
(* 7.8c *)


Lemma pf78c1 f : f \in irr G -> 
  (forall psi, psi \in calS -> '[nu psi, f]_G = 0) ->
  {in A, forall x, f^\rho x = '[beta, f]_G}.
Proof.
move => f_irr f_ortho x xA.
have fZ: f \in 'Z[irr G] by case/irrP: f_irr => t ->; rewrite irr_vchar.
rewrite (pf77a (ind_irrs1_subset chiS) _ xA).
rewrite (bigID (pred1 ('Ind[L, K] 1))) /= big_pred1_uniq ?uniq_ind_irrs ?one_in_ind_irrs //.
rewrite big1_seq; last first.
  move => g /andP [g_n_1 g_zi].
  have gS: g \in calS by rewrite mem_filter /= g_n_1 g_zi.
  rewrite chi1 -nu_tau ?ind_irrs1_sub_e_vchar // raddf_sub raddfMZ ?ind_irrs1_1eZ //.
  rewrite cfdot_subl !cfdotZl.
  by rewrite !f_ortho // mulr0 subrr conjC0 !mul0r.
rewrite cfInd_cfun1 // !cfunE !cfuniE // in_group.
rewrite in_setD1 in xA; move/andP: xA => [_] ->.
rewrite [e * true%:R]mulr1 chi1 mulfV // scale1r.
rewrite -cfInd_cfun1 // cfnorm_Ind1 // divfK // addr0.
by rewrite isIntC_conj // cfdot_vchar_Int // Dade_vchar // pre_beta_vchar.
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
by rewrite isIntC_conj ?cfdot_vchar_Int // Dade_vchar ?pre_beta_vchar.
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
Local Notation calS i := (induced_irrs1 (KK i) (LL i)).
Local Notation e i := (#|LL i : KK i|%:R : algC).

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

Hypothesis chiS : forall i, 'chi_(r i) \in calS i.
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
rewrite Dade_conjC ?pre_beta_memc ?chi1 ?chiS //.
rewrite -linear_sub rmorph_sub /= conj_cfInd cfConjC1.
rewrite addrAC oppr_add addrA subrr opprK add0r.
pose S := [:: 'chi_(r i); (('chi_(r i))^*)%CF].
have sSS : {subset S <= calS i}.
  by move => f; rewrite !inE; case/orP => /eqP ->; rewrite ?ind_irrs1_conjC ?chiS.
have freeS: free S.
  have := ind_irrs1_conjC_ortho2 (nKL i) (oddSg (sLG i) oddG) (chiS i).
  exact: orthonormal_free.
have sSZ X : {subset 'Z[S, X] <= 'Z[calS i, X]}.
  apply: vchar_subset => //; exact: free_ind_irrs1.
rewrite (@pf59a _ _ _ _ _ (ddI i) conjC S (nu i) 'chi_(r i)) //.
- by rewrite -nu_tau ?raddf_sub ?ind_irrs1_sub_conjC_vchar ?chiS.
- by move => f; rewrite !inE; case/orP => /eqP ->; rewrite ?cfConjC_irr ?irr_chi.
- move => f; rewrite vchar_split [in X in _ = X]vchar_split !cfun_onE.
  apply/andP/andP => [] []; last first.
    move => -> fA1; apply/andP; rewrite (subset_trans fA1) //.
    by apply/subsetP => x; rewrite !inE => /andP [] -> /(subsetP (sKL i)) ->.
  move => fZ fL; rewrite fZ; apply/andP; rewrite andTb.
  apply/subsetP => x; apply: contraR.
  rewrite !inE negb_and negbK; case/orP => [/eqP -> | xnK].
    by rewrite (supportP fL) // !inE negb_and negbK eqxx orTb.
  have /coord_span/cfunP/(_ x) := vchar_span fZ.
  rewrite sum_cfunE => -> /=; apply/eqP.
  apply: big1 => j _; apply/eqP.
  rewrite cfunE mulf_eq0; apply/orP; right.
  have: S`_j \in S by exact: mem_nth.
  by rewrite !inE; case/orP => /eqP ->;
    rewrite (supportP (support_ind_irrs1 (nKL i) _) _ xnK) ?ind_irrs1_conjC ?chiS.
- by move => f; rewrite !inE; case/orP => /eqP ->; 
    rewrite ?cfConjCK eqxx ?orbT ?orTb.
- by move => f /sSZ; exact: nu_to.
- by move => f g /sSZ fZ /sSZ gZ ; exact: nu_isom.
- by move => f /sSZ; exact: nu_tau.
by rewrite inE eqxx.
Qed.

Let d_ortho1 i : '[d i, 1]_G = 0.
Proof.
rewrite !cfdotDl cfdotNl.
rewrite (dot_beta_1 (ddI i)) ?chiS ?chi1 //.
rewrite (@pf78a1 _ _ _ (ddI i) _ (nu i) (r i)) ?chiS //.
by rewrite cfnorm1 subrr addr0.
Qed.

Let beta12_ortho i j : i != j -> '[beta i, beta j]_G = 0.
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
  apply/orthonormal2P; rewrite ?memc_Zirr ?nu_to ?ind_irrs1_vcharW ?ind_irrs1_conjC //.
  split; rewrite nu_isom ?ind_irrs1_vcharW ?ind_irrs1_conjC // ?cfdot_irr ?eqxx ?chiS //.
    by rewrite (ind_irrs1_conjC_ortho (nKL a)) ?chiS ?(oddSg (sLG a) oddG).
  by rewrite -conj_cfdot cfdot_irr eqxx conjC1.
have sSZirr a : {subset S a <= 'Z[irr G]}.
  by move => f; rewrite 2!inE; case/orP => /eqP ->;
    rewrite nu_to ?ind_irrs1_vcharW ?ind_irrs1_conjC ?chiS.
have/(_ 1 1) := vchar_pairs_orthonormal (conj (sSZirr i) (sSZirr j)).
rewrite !S_ortho nonzero1r (isIntC_Real (isIntC_nat 1)) /=.
rewrite !scale1r -!raddf_sub.
rewrite [(nu i) (_ - _)]nu_tau ?[(nu j) (_ - _)]nu_tau ?ind_irrs1_sub_conjC_vchar ?chiS //.
rewrite !Dade1 eqxx.
set prod := '[_, _]_G.
have ->: prod == 0.
  rewrite /prod (@cfdot_complement _ G (Atau i)) //.
    by rewrite Dade_cfunS ?vchar_on ?sub_vchar_cconj 1?vchar_split 
      ?(support_ind_irrs1 (nKL i)) ?irr_vchar.
  set mu := _ - _.
  have: mu^\tau_j \in 'CF(G, Atau j).
    by rewrite Dade_cfunS ?vchar_on ?sub_vchar_cconj 1?vchar_split
      ?(support_ind_irrs1 (nKL j)) ?irr_vchar.
  rewrite cfun_onE [in X in _ -> X]cfun_onE => sA.
  apply: (subset_trans sA).
  by rewrite subsetD disjoint_sym (disjointAtau i_n_j) Dade_support_sub.
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
  rewrite !add_vchar // ?opp_vchar -?chi0_1 ?irr_vchar // ?Dade_vchar ?pre_beta_vchar //.
  by rewrite nu_to ?ind_irrs1_vcharW ?chiS.
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
do 2 rewrite cfdotC conj_cfdot cfConjCK cfdotC mulrC.
by rewrite !d_conjC !isIntC_conj // cfdot_vchar_Int ?irr_vchar.
Qed.


Lemma pf79 i j : i != j -> 
  ('[beta i, nu j 'chi_(r j)]_G != 0) || ('[beta j, nu i 'chi_(r i)]_G != 0).
Proof.
move => i_n_j.
have/eqP : '[beta i, nu j 'chi_(r j)]_G + '[beta j, nu i 'chi_(r i)]_G = 1 + '[d i, d j]_G.
  rewrite !cfdotDl !cfdotDr !cfdotNl !cfdotNr.
  rewrite beta12_ortho // (dot_beta_1 (ddI i)) // nu_chi12_ortho //.
  rewrite !addrA !addr0 subrr add0r -!addrA; congr (_ + _); symmetry.
  rewrite cfdotC (dot_beta_1 (ddI j)) // cfnorm1.
  rewrite opprK !addrA conjC1 addNr add0r.
  rewrite cfdotC (@pf78a1 _ _ _ (ddI j) _ (nu j) (r j)) ?chiS //.
  rewrite (@pf78a1 _ _ _ (ddI i) _ (nu i) (r i)) ?chiS //.
  rewrite conjC0 oppr0 add0r addr0 cfdotC isIntC_conj //.
  by rewrite cfdot_vchar_Int ?nu_to ?Dade_vchar ?pre_beta_vchar // ind_irrs1_vcharW ?chiS.
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

Local Notation S i := (induced_irrs1 (KK i) (LL i)).

Let r (i : 'I_k) := odflt 0 [pick j : Iirr (LL i) | ('chi_j \in S i) && ('chi_j 1%g == e i)].

Let i1 := arg_min (Ordinal k_ge2) predT (fun i => #|KK i|).

(* Properties of the defined objects *)

Let i1_prop i : h i1 <= h i.
Proof.
rewrite -leq_leC.
have := @arg_minP _ (Ordinal k_ge2) predT (fun i => #|KK i|).
by rewrite -/i1 => /(_ isT); case => j _ /(_ i isT).
Qed.

(* This follows from Isaacs 6.34 *)
Let sSirrL i : {subset S i <= irr (LL i)}.
Proof.
move => f; rewrite mem_filter inE => /andP [f_n1 /ind_irrsP [t f_t]].
rewrite f_t irr_induced_Frobenius_ker //.
  by apply: contra f_n1; rewrite f_t -chi0_1 => /eqP ->.
exact: (Frobenius_cent1_ker (frobeniusL i)).
Qed.

Let chi_exists i : exists2 xi, xi \in S i & xi 1%g = e i.
Proof.
have/Frobenius_context [_ Kn1 _ _ _] := frobeniusL i.
have solK : solvable (KK i) by exact: (solvableS (sKL i)).
case: (lin_char_solvable Kn1 solK) => t linear_t t_n1.
exists ('Ind[LL i, KK i] 'chi_t); last first.
  rewrite cfInd1 // -/(e i).
  by move/andP: linear_t => [_ /eqP] ->; rewrite mulr1.
rewrite mem_filter inE; apply/andP; split; last by apply/ind_irrsP; exists t.
have := cfclass_irr_induced 0 t (nKL i).
rewrite chi0_1 cfclass1 // inE (negPf t_n1).
move/eqP; apply: contraL => /eqP ->.
by rewrite cfnorm_eq0 cfInd_eq0 ?cfun1_char // nonzero1r.
Qed.

Let chiS i : 'chi_(r i) \in S i.
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
Proof. by move => fS; rewrite nu_isom ?ind_irrs1_vcharW // normS. Qed.


Lemma isIntC_normC_ge1 a : isIntC a -> a != 0 -> 1 <= `|a|.
Proof.
rewrite isIntCE; case/orP; case/isNatCP => n.
  by move ->; case: n => [| n]; rewrite ?eqxx // normC_nat -(leq_leC 1).
move/eqP; rewrite eqr_oppC => /eqP ->; rewrite normC_opp oppr_eq0 normC_nat.
by case: n => [| n]; rewrite ?eqxx // -(leq_leC 1).
Qed.

Lemma isIntC_expr2_ge1 a : isIntC a -> a != 0 -> 1 <= a ^+ 2.
Proof.
move => aZ /(isIntC_normC_ge1 aZ) abs_a; rewrite -int_normCK //.
have ->: 1 = ((1 : algC) ^+ 2) by rewrite expr2 mulr1.
by rewrite leC_square // posC1.
Qed.


Let nu_ij_ortho i j f g : i != j -> f \in S i -> g \in S j ->
  '[(nu i) f, (nu j) g]_G = 0.
Proof.
move => i_n_j fS gS.
pose X a u := [:: (nu a) u; (nu a) ((u^*)%CF)].
have X_ortho a u : u \in S a -> orthonormal (X a u).
  move => uS; case/irrP: (sSirrL uS) => q xi_q.
  apply/orthonormal2P; rewrite ?memc_Zirr ?nu_to ?ind_irrs1_vcharW ?ind_irrs1_conjC //.
  split; rewrite nu_isom ?ind_irrs1_vcharW ?ind_irrs1_conjC // xi_q ?cfdot_irr ?eqxx //.
    by rewrite (ind_irrs1_conjC_ortho (nKL a)) ?(oddSg (sLG a) oddG) // -xi_q.
  by rewrite -conjC_IirrE cfdot_irr eqxx.
have sXZirr a u : u \in S a -> {subset X a u <= 'Z[irr G]}.
  by move => uS ff; rewrite 2!inE; case/orP => /eqP ->;
    rewrite nu_to ?ind_irrs1_vcharW ?ind_irrs1_conjC.
have/(_ 1 1) := vchar_pairs_orthonormal (conj (sXZirr i f fS) (sXZirr j g gS)).
rewrite !X_ortho // nonzero1r (isIntC_Real (isIntC_nat 1)) /=.
rewrite !scale1r -!raddf_sub.
rewrite [(nu i) (_ - _)]nu_tau ?[(nu j) (_ - _)]nu_tau ?ind_irrs1_sub_conjC_vchar //.
rewrite !Dade1 eqxx.
set prod := '[_, _]_G.
have ->: prod == 0.
  rewrite /prod (@cfdot_complement _ G (Atau i)) //.
    by rewrite Dade_cfunS ?vchar_on ?sub_vchar_cconj 1?vchar_split //.
  set mu := _ - _.
  have: (tau j) mu \in 'CF(G, Atau j).
    by rewrite Dade_cfunS ?vchar_on ?sub_vchar_cconj 1?vchar_split //.
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
  by rewrite nu_to ?ind_irrs1_vcharW ?chiS.
case: (vchar_norm1P nu_chi1_Z (norm_nuS (chiS i1))) => eps [t] nu_chi1_irr.
have: #|G|%:R ^-1 * (#|G0|%:R - \sum_(g \in G0) `|'chi_t g| ^+ 2) <= rhs.
  rewrite mulrC leC_pmul2r ?sposC_inv ?sposGC // leC_add2l leC_opp G0_def.
  rewrite (big_setD1 1%g) /=; last first.
    rewrite inE in_group andbT; apply: contraT; rewrite negbK.
    case/bigcupP => i _; rewrite Dade_supp class_supportEr.
    by case/bigcupP => x _; rewrite conjD1g !inE eqxx andFb.
  rewrite -[1]addr0 leC_add //; last first.
    by apply: posC_sum => g _; rewrite -normC_exp posC_norm.
  have rZ: isIntC ('chi_t 1%g) by rewrite isIntCE; apply/orP; left; exact: isNatC_irr1.
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
  have {X}->: X = '[(rho i1) (nu1 ('chi_(r i1)))]_(LL i1).
    rewrite /X nu_chi1_irr linearZ cfnormZ int_normCK ?isIntC_sign //= sqr_sign.
    by rewrite mul1r rho_eq.
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
  move => f fS; have := nu_ij_ortho i_n1 fS (chiS i1).
  rewrite nu_chi1_irr cfdotZr => /eqP; rewrite mulf_eq0; case/orP.
    by rewrite conjC_eq0 signr_eq0.
  by move/eqP.
rewrite -leC_sub -{2}[_ / _]mulr1 -mulr_subr subr0 !posC_mul ?posC_inv ?posC_nat //.
rewrite leC_sub isIntC_expr2_ge1 //.
  by rewrite cfdot_vchar_Int ?irr_vchar ?Dade_vchar ?pre_beta_vchar ?chi1.
move: beta_chi_n0; rewrite nu_chi1_irr cfdotZr mulf_eq0 negb_or.
by move/andP => [].
Qed.


(**************************************)

Let ineq2 : \sum_(i \in calB) (h i - 1) / (e i) <= e1 - 1.
Proof.
have := pf78a2 (nKL i1) (chiS i1) (chi1 i1) (S_non_trivial i1)
           (@nu_isom i1) (@nu_to i1) (@nu_tau i1).
rewrite -/e1.
move => [a] [Gamma] [] _ Gamma1 Gamma_nu beta_eq.
have fe_nat i f: f \in S i -> exists m, (f 1%g / e i) = m%:R.
  move => fS; apply/isNatCP; case/ind_irrs1P: fS => t -> _.
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
    rewrite cfdot_suml (bigD1 i) //=.
    rewrite cfdotZl cfdot_suml (bigID (pred1 f)) /=.
    rewrite big_pred1_uniq ?uniq_ind_irrs1 // big1_seq; last first.
      move => g /andP [g_n_f gS]; rewrite cfdotZl.
        by rewrite nu_isom ?ind_irrs1_vcharW // (ind_irrs1_ortho (nKL i)) // mulr0.
    rewrite addr0 cfdotZl norm_nuS // mulr1 mulrC.
    rewrite big1 ?addr0 // => j /andP [_ j_n_i].
    rewrite cfdotZl cfdot_suml big1_seq ?mulr0 // => g /andP [_ gS].
    by rewrite cfdotZl nu_ij_ortho ?mulr0.
  have ->: '[Gamma, (nu i) f]_G = '[beta i1, (nu i) f]_G.
    rewrite /beta beta_eq !cfdotDl cfdotNl cfdotZl.
    rewrite nu_ij_ortho ?chiS //; last by rewrite eq_sym.
    rewrite ['[1, _]_G]cfdotC.
    rewrite (@pf78a1 (KK i) (LL i) DadeH _ _ (nu i) (r i)) ?chi1 //.
    rewrite conjC0 addr0 subr0 addrC; apply/esym.
    rewrite cfdot_suml big1_seq ?mulr0 ?add0r // => g /andP [_ gS].
    by rewrite cfdotZl nu_ij_ortho ?mulr0 // eq_sym.
  have [m fe_m] := fe_nat i f fS.
  rewrite /cx fe_m -conjC_nat -cfdotZr -cfdotNr -cfdotDr.
  rewrite scaler_nat -raddfMn -raddf_sub nu_tau //; last first.
    by rewrite -scaler_nat -fe_m ind_irrs1_sub_e_vchar ?chi1.
  rewrite (@cfdot_complement _ G (Atau i1)) //.
    by rewrite Dade_cfunS ?vchar_on ?pre_beta_vchar ?chi1.
  have: (tau i) (f - 'chi_(r i) *+ m) \in 'CF(G, Atau i).
    by rewrite Dade_cfunS ?vchar_on // -scaler_nat -fe_m.
  rewrite !cfun_onE => sA; apply: (subset_trans sA).
  by rewrite subsetD disjoint_Atau // Dade_support_sub.
have norm_X : '[X]_G <= e1 - 1.
  have := pf78b2 (nKL i1) (chiS i1) (chi1 i1) (S_non_trivial i1)
             (@nu_isom i1) (@nu_to i1) (@nu_tau i1) (eh_ineq i1) Gamma1 Gamma_nu beta_eq.
  rewrite -/e1; apply: leC_trans.
  have ->: Gamma = (Gamma - X) + X by rewrite subrK.
  by rewrite cfnormD X_ortho conjC0 !addr0 -leC_sub addrK cfnorm_posC.
apply: leC_trans norm_X.
have x_Z i : isIntC (cx i).
  by rewrite /cx cfdot_vchar_Int ?nu_to ?ind_irrs1_vcharW ?Dade_vchar ?pre_beta_vchar ?chi1 ?chiS.
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
  rewrite (bigID (pred1 f)) /= big_pred1_uniq ?uniq_ind_irrs1 // big1_seq.
    rewrite addr0 cfnormZ fe_m normC_nat.
    by rewrite norm_nuS ?normS // invr1.
  move => g /andP [g_n_f] gS; rewrite cfdotZl cfdotZr.
  by rewrite nu_isom ?ind_irrs1_vcharW // (ind_irrs1_ortho (nKL i)) // !mulr0.
rewrite -[\sum_(i \in calB) _]addr0 [in X in _ <= X](bigID calB) /=.
rewrite leC_add //; last first.
  apply: posC_sum => i _; rewrite -int_normCK // -normC_exp posC_mul ?posC_norm //.
  rewrite big_seq posC_sum // => f fS; case: (fe_nat i f fS) => m ->.
  by rewrite posC_mul ?posC_inv ?cfnorm_posC // expr2 posC_mul ?posC_nat.
have ->: \sum_(i \in calB) (h i - 1) / e i =
  \sum_(i < k | [&& i != i1, '[beta i, nu1 ('chi_(r i1))]_G == 0 & i != i1]) (h i - 1) / e i.
    by apply: eq_bigl => i; rewrite /calB !inE; apply/idP/idP; move/andP => [] -> ->.
rewrite -leC_sub -sumr_sub posC_sum // => i /and3P [] i_n_1 beta_nu0 _.
rewrite ind_irrs1_sum1 // -/(e i) -/(h i).
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
  have := pf79 oddG Dade_disj nKL S_non_trivial nu_isom nu_to nu_tauI chiS chi1 i_n_1.
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
  (e i - 1) * ((h i - 2%:R * e i - 1) / (e i * h i) + 2%:R / (h i * (h i + 2%:R))) <=
    (#|G0|%:R - 1) / #|G|%:R.
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

