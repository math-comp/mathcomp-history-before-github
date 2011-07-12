(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import mxpoly mxrepresentation vector algC classfun character.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file provides basic notions of virtual character theory:              *)
(* 'Z[S, A]      : integer combinations of elements of S : seq 'CF(G) that    *)
(*                 have support in A.                                         *)
(* 'Z[T]         : integer combinations of elements S                         *)
(******************************************************************************)

Definition virtual_char (gT : finGroupType) (B : {set gT})
                        (S : seq 'CF(B)) (A : {set gT}) :=
  [pred phi \in span S | [&& forallb i, isZC (coord (in_tuple S) phi i)
                           & support phi \subset A]].

Notation "''Z[' S , A ]" := (virtual_char S A)
  (at level 8, format "''Z[' S ,  A ]") : group_scope. 
Notation "''Z[' S ]" := 'Z[S, setT]
  (at level 8, format "''Z[' S ]") : group_scope.

Section IsVChar.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (A : {set gT}) (phi chi : 'CF(G)) (S : seq 'CF(G)).

Lemma vcharP phi :
  reflect (exists2 chi1, is_char chi1 & exists2 chi2, is_char chi2
                       & phi = chi1 - chi2)
          (phi \in 'Z[irr G]).
Proof.
rewrite 2!inE tvalK /tcast; case: _ / (esym _).
have /andP[/(span _ =P _)-> _] := is_basis_irr G.
apply: (iffP and3P) => [[_ VCphi _]|[chi1 Nchi1 [chi2 Nchi2 ->]]]; last first.
  split=> //; first exact: memvf.
  apply/forallP=> i; rewrite linearD linearN !ffunE !coord_cfdot.
  by rewrite isZC_add ?isZC_opp // isZCE isNatC_cfdot_char_irr.
pose Nphi i := isNatC('[phi, 'chi_i]).
rewrite [phi]cfun_cfdot_sum (bigID Nphi) /= -[rh in _ + rh]opprK -sumr_opp.
set chi1 := \sum_(i | _) _; set chi2 := \sum_(i | _) _; exists chi1.
  by apply: is_char_sum => i /is_char_scale-> //; exact: is_char_irr.
exists chi2 => //; apply: is_char_sum => i /negbTE notNphi_i.
rewrite -scaleNr is_char_scale ?is_char_irr //.
by have:= forallP VCphi i; rewrite coord_cfdot isZCE [isNatC _]notNphi_i.
Qed.

Lemma vchar_char chi : is_char chi -> chi \in 'Z[irr G].
Proof.
move=> Nchi; apply/vcharP; exists chi => //.
by exists 0; rewrite ?is_char0 ?subr0.
Qed.

Lemma vchar_irr i : 'chi[G]_i \in 'Z[irr G].
Proof. by apply: vchar_char; apply: is_char_irr. Qed.

Lemma support_vchar S A phi : phi \in 'Z[S, A] -> support phi \subset A.
Proof. by case/and3P. Qed.

Lemma span_vchar S A : {subset 'Z[S, A] <= span S}.
Proof. by move=> phi /and3P[]. Qed.

Lemma vcharW S A : {subset 'Z[S, A] <= 'Z[S]}.
Proof. by move=> phi /and3P[Sf VCf _]; exact/and3P. Qed.

Lemma vchar_split S A phi :
  phi \in 'Z[S, A] = (phi \in 'Z[S]) && (support phi \subset A).
Proof. by rewrite !inE subsetT_hint -!andbA. Qed.

Lemma memc_vchar A : {subset 'Z[irr G, A] <= 'CF(G, A)}.
Proof. by move=> phi /support_vchar; rewrite memcE. Qed.

Lemma memv_vchar S A phi : 
  free S -> support phi \subset A -> phi \in S -> phi \in 'Z[S, A].
Proof.
move=> freeS Aphi Sphi; apply/and3P; split=> //; first exact: memv_span.
have lt_phi_S: (index phi S < size S)%N by rewrite index_mem.
apply/forallP=> i; rewrite -(nth_index 0 Sphi) (free_coordt (Ordinal _)) //.
exact: isZC_nat.
Qed.

Lemma isZC_cfdot_vchar_irr i phi : phi \in 'Z[irr G] -> isZC ('[phi, 'chi_i]).
Proof.
move=> VCphi; have /and3P[_ /forallP] := VCphi.
by rewrite tvalK /tcast -coord_cfdot; case: _ / (esym _) => ->.
Qed.

Lemma isZC_coord_vchar m (S : m.-tuple _) A phi i : 
  phi \in 'Z[S, A] -> isZC (coord S phi i).
Proof. by case/and3P; rewrite tvalK; case: _ / (esym _) => _ /forallP->. Qed.

Lemma cfdot_vchar_r phi psi :
  psi \in 'Z[irr G] -> '[phi, psi] = \sum_i '[phi, 'chi_i] * '[psi, 'chi_i].
Proof.
move=> VCpsi; rewrite cfdot_sum_irr; apply: eq_bigr => i _; congr (_ * _).
by rewrite isZC_conj ?isZC_cfdot_vchar_irr.
Qed.

Lemma isZC_cfdot_vchar : {in 'Z[irr G] &, forall phi psi, isZC '[phi, psi]}.
Proof.
move=> phi psi Zphi Zpsi; rewrite /= cfdot_vchar_r // isZC_sum // => k _.
by rewrite isZC_mul ?isZC_cfdot_vchar_irr.
Qed.

Lemma isNatC_cfnorm_vchar : {in 'Z[irr G], forall phi, isNatC '[phi]}.
Proof.
by move=> phi Zphi; rewrite /= isNatC_Zpos posC_cfnorm isZC_cfdot_vchar.
Qed.

Lemma vchar0 S A : 0 \in 'Z[S, A].
Proof.
rewrite !inE; apply/and3P; split; first by apply: mem0v.
  by apply/forallP=> i; rewrite linear0 ffunE (isZC_nat 0). 
by apply/subsetP=> x; rewrite !inE cfunE eqxx.
Qed.

Lemma vchar_opp S A phi : (- phi \in 'Z[S, A]) = (phi \in 'Z[S, A]).
Proof.
wlog suff: phi / phi \in 'Z[S, A] -> - phi \in 'Z[S, A].
  by move=> IH; apply/idP/idP=> /IH //; rewrite opprK.
case/and3P=> Sphi /forallP VCphi Aphi; rewrite !inE memvN {}Sphi linearN /=.
apply/andP; split; first by apply/forallP=> i; rewrite ffunE isZC_opp.
by apply: etrans Aphi; apply: eq_subset => a; rewrite !inE cfunE oppr_eq0.
Qed.

Lemma vchar_add S A phi psi :
  phi \in 'Z[S, A]-> psi \in 'Z[S, A]-> (phi + psi) \in 'Z[S, A].
Proof.
case/and3P=> Sphi /forallP VCphi; rewrite -memcE => Aphi.
case/and3P=> Spsi /forallP VCpsi; rewrite -memcE => Apsi.
rewrite !inE -memcE !memvD //= andbT.
by apply/forallP=> a; rewrite linearD ffunE isZC_add.
Qed.

Lemma vchar_sub S A phi psi : 
   phi \in 'Z[S, A] -> psi \in 'Z[S, A] -> (phi - psi) \in 'Z[S, A]. 
Proof. by move=> VCphi VCpsi; rewrite vchar_add ?vchar_opp. Qed.

Lemma vchar_scal S A phi n : phi \in 'Z[S, A] -> (phi *+ n) \in 'Z[S, A].
Proof.
by move=> VCphi; elim: n => [|n Hn]; rewrite ?vchar0 // mulrS vchar_add.
Qed.

Lemma vchar_scaln S A phi n : phi \in 'Z[S, A] -> (phi *- n) \in 'Z[S, A].
Proof. by move=> Hphi; rewrite vchar_opp vchar_scal. Qed.

Lemma vchar_sign S A phi n :
  ((-1) ^+ n *: phi \in 'Z[S, A]) = (phi \in 'Z[S, A]).
Proof. by rewrite -signr_odd scaler_sign; case: ifP; rewrite ?vchar_opp. Qed.

Lemma vchar_scalZ S A phi a :
  isZC a -> phi \in 'Z[S, A] -> a *: phi \in 'Z[S, A].
Proof.
move/eqP=> -> /vchar_scal Sphi.
by case: getZC => [b n]; rewrite -scalerA vchar_sign scaler_nat Sphi.
Qed.

Lemma vchar_sum S A I r (P : pred I) F :
  (forall i, P i -> F i \in 'Z[S, A]) -> \sum_(i <- r | P i) F i \in 'Z[S, A].
Proof.
move=> S_F; elim/big_rec: _ => [|i phi Pi Sphi]; first exact: vchar0.
by rewrite vchar_add ?S_F.
Qed.

Lemma vchar_mul phi psi A : 
  phi \in 'Z[irr G, A]-> psi \in 'Z[irr G, A]-> phi * psi \in 'Z[irr G, A].
Proof.
rewrite !(vchar_split _ A) => /andP[/vcharP[xi1 Nxi1 [xi2 Nxi2 def_phi]] Aphi].
case/andP=> [/vcharP[xi3 Cxi3 [xi4 Nxi4 ->]] _].
apply/andP; split; last first.
  apply/subsetP=> a; rewrite !inE; apply: contraR => notAa.
  by rewrite cfunE (supportP Aphi) ?mul0r.
have isch := (is_char_add, is_char_mul); apply/vcharP.
exists (xi1 * xi3 + xi2 * xi4); first by rewrite !isch.
exists (xi1 * xi4 + xi2 * xi3); first by rewrite !isch.
by rewrite mulr_subr def_phi !mulr_subl addrAC oppr_sub -!addrA -oppr_add.
Qed.

Lemma vchar_trans S1 S2 A B :
    free S1 -> free S2 -> {subset S1 <= 'Z[S2, B]} ->
  {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS1 freeS2 sS12 phi /and3P[S1pfi VCphi Aphi].
rewrite !inE {}Aphi andbT (@coord_span _ _ _ (in_tuple S1) phi) //.
rewrite memv_suml // => [|i _]; last first.
  by rewrite memvZ (span_vchar (sS12 _ _)) ?mem_nth ?orbT.
apply/forallP=> i; rewrite coord_sumE isZC_sum // => j _.
rewrite linearZ !ffunE /= isZC_mul ?(forallP VCphi) //.
by have/and3P[_ /forallP-> _]: S1`_j \in 'Z[S2, B] by rewrite sS12 ?mem_nth.
Qed.

Lemma vchar_sub_irr S A :
  free S -> {subset S <= 'Z[irr G]} -> {subset 'Z[S, A] <= 'Z[irr G, A]}.
Proof. by move/vchar_trans; apply; exact: free_irr. Qed.

Lemma vchar_subset S1 S2 A :
  free S1 -> free S2 -> {subset S1 <= S2} -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS1 freeS2 sS12; apply: vchar_trans setT _ _ _ => // f /sS12 S2f.
exact: memv_vchar.
Qed.

Lemma vchar_subseq S1 S2 A :
  free S2 -> subseq S1 S2 -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS2 sS12; apply: vchar_subset (mem_subseq sS12) => //.
by rewrite (subseq_uniqP (uniq_free freeS2) sS12) free_filter.
Qed.

Lemma vchar_filter S A (p : pred 'CF(G)) :
  free S -> {subset 'Z[filter p S, A] <= 'Z[S, A]}.
Proof.
move=> freeS; apply: vchar_subset; rewrite ?free_filter // => f.
by rewrite mem_filter => /andP[].
Qed.

Lemma cfnorm_sign n phi : '[(-1) ^+ n *: phi] = '[phi].
Proof. by rewrite -signr_odd scaler_sign; case: (odd n); rewrite ?cfnormN. Qed.

Lemma vchar_orthonormalP (S : seq 'CF(G)) :
    {subset S <= 'Z[irr G]} ->
  reflect (exists I : {set Iirr G}, exists b : Iirr G -> bool,
           perm_eq S [seq (-1) ^+ b i *: 'chi_i | i <- enum I])
          (orthonormal S).
Proof.
move=> vcS; apply: (equivP (orthonormalP _)).
split=> [[uniqS oSS] | [I [b defS]]]; last first.
  split=> [|xi1 xi2]; rewrite ?(perm_eq_mem defS).
    rewrite (perm_eq_uniq defS) map_inj_uniq ?enum_uniq // => i j /eqP.
    by rewrite eq_signed_irr => /andP[_ /eqP].
  case/mapP=> [i _ ->] /mapP[j _ ->]; rewrite eq_signed_irr.
  rewrite cfdotZl cfdotZr rmorph_sign mulrA cfdot_irr -signr_addb mulr_natr.
  by rewrite mulrb andbC; case: eqP => //= ->; rewrite addbb eqxx.
pose I := [set i | ('chi_i \in S) || (- 'chi_i \in S)].
pose b i := - 'chi_i \in S; exists I, b.
apply: uniq_perm_eq => // [|xi].
  rewrite map_inj_uniq ?enum_uniq // => i j /eqP.
  by rewrite eq_signed_irr => /andP[_ /eqP].
apply/idP/mapP=> [Sxi | [i Ii ->{xi}]]; last first.
  move: Ii; rewrite mem_enum inE orbC -/(b i).
  by case b_i: (b i); rewrite (scale1r, scaleN1r).
have: '[xi] = 1 by rewrite oSS ?eqxx.
have vc_xi := vcS _ Sxi; rewrite cfdot_sum_irr.
case/isNatC_sum_eq1 => [i _ | i [_ /eqP norm_xi_i xi_i'_0]].
  by rewrite -normCK ?isNatC_mul ?normCZ_nat ?isZC_cfdot_vchar_irr.
suffices def_xi: xi = (-1) ^+ b i *: 'chi_i.
  exists i; rewrite // mem_enum inE -/(b i) orbC.
  by case: (b i) def_xi Sxi => // ->; rewrite scale1r.
move: Sxi; rewrite [xi]cfun_cfdot_sum (bigD1 i) //.
rewrite big1 //= ?addr0 => [|j ne_ji]; last first.
  apply/eqP; rewrite scalev_eq0 -normC_eq0 -[_ == 0](expf_eq0 _ 2) normCK.
  by rewrite xi_i'_0 ?eqxx.
have:= norm_xi_i; rewrite (isZC_conj (isZC_cfdot_vchar_irr _ _)) //.
rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0 /b scaler_sign.
case/pred2P=> ->; last by rewrite scaleN1r => ->.
rewrite scale1r => Sxi; case: ifP => // SNxi.
have:= oSS _ _ Sxi SNxi; rewrite cfdotNr cfdot_irr eqxx; case: eqP => // _.
by move/eqP; rewrite oppr_eq0 oner_eq0.
Qed.

Lemma vchar_norm1P phi :
    phi \in 'Z[irr G] -> '[phi] = 1 ->
  exists b : bool, exists i : Iirr G, phi = (-1) ^+ b *: 'chi_i.
Proof.
move=> Zphi phiN1.
have: orthonormal phi by rewrite /orthonormal/= -cfnorm_eq0 phiN1 eqxx oner_eq0.
case/vchar_orthonormalP=> [xi /predU1P[->|] // | I [b def_phi]].
have: phi \in (phi : seq _) := mem_head _ _.
by rewrite (perm_eq_mem def_phi) => /mapP[i _ ->]; exists (b i), i.
Qed.

Lemma vchar_small_norm phi n :
    phi \in 'Z[irr G] -> '[phi] = n%:R -> (n < 4)%N ->
  exists S : n.-tuple 'CF(G),
    [/\ orthonormal S, {subset S <= 'Z[irr G]} & phi = \sum_(xi <- S) xi].
Proof.
move=> Zphi def_n lt_n_4.
pose S := [seq '[phi, 'chi_i] *: 'chi_i | i <- enum [pred i | is_comp i phi]].
have def_phi: phi = \sum_(xi <- S) xi.
  rewrite big_map /= big_filter big_mkcond {1}[phi]cfun_cfdot_sum.
  by apply: eq_bigr => i _; rewrite if_neg; case: eqP => // ->; rewrite scale0r.
have orthS: orthonormal S.
  apply/orthonormalP; split=> [|_ _ /mapP[i phi_i ->] /mapP[j _ ->]].
    rewrite map_inj_in_uniq ?enum_uniq // => i j; rewrite mem_enum => phi_i _.
    by move/eqP; rewrite eq_scaled_irr (negbTE phi_i) => /andP[_ /= /eqP].
  rewrite eq_scaled_irr cfdotZl cfdotZr cfdot_irr mulrA mulr_natr mulrb.
  rewrite mem_enum in phi_i; rewrite (negbTE phi_i) andbC; case: eqP => // <-.
  have /isNatCP[m def_m] := normCZ_nat (isZC_cfdot_vchar_irr i Zphi).
  apply/eqP; rewrite eqxx /= -normCK def_m -natr_exp -eqN_eqC eqn_leq lt0n.
  rewrite expn_eq0 andbT eqN_eqC -def_m normC_eq0 [~~ _]phi_i andbT.
  rewrite (leq_exp2r _ 1) // -ltnS -(@ltn_exp2r _ _ 2) //.
  apply: leq_ltn_trans lt_n_4; rewrite leq_leC -def_n natr_exp.
  rewrite cfdot_sum_irr (bigD1 i) //= -normCK def_m addrC -leC_sub addrK.
  by rewrite posC_sum // => ? _; exact: posC_pconj.
have <-: size S = n.
  apply/eqP; rewrite eqN_eqC -def_n def_phi.
  have [/allP N1_S oS] := andP orthS; rewrite cfnorm_orthogonal // big_tnth.
  rewrite (eq_bigr (fun k => 1)) ?sumr_const ?card_ord // => k _.
  by rewrite (eqP (N1_S _ _)) ?mem_tnth.
exists (in_tuple S); split=> // _ /mapP[i _ ->].
by rewrite vchar_scalZ ?vchar_irr // isZC_cfdot_vchar_irr.
Qed.

Lemma vchar_norm2 phi :
    phi \in 'Z[irr G, G^#] -> '[phi] = 2%:R ->
  exists i, exists2 j, j != i & phi = 'chi_i - 'chi_j.
Proof.
rewrite vchar_split => /andP[Zphi phi1_0].
case/vchar_small_norm => // [[[|chi [|xi [|?]]] //= S2]].
case=> /andP[/and3P[Nchi Nxi _] /and3P[_ ochi _]] /allP/and3P[Zchi Zxi _].
rewrite big_cons big_seq1 => def_phi.
have [b [i def_chi]] := vchar_norm1P Zchi (eqP Nchi).
have [c [j def_xi]] := vchar_norm1P Zxi (eqP Nxi).
have neq_ji: j != i.
  apply: contraTneq ochi; rewrite /orthogonal /= !andbT def_chi def_xi => ->.
  rewrite cfdotZl cfdotZr rmorph_sign cfdot_irr eqxx mulr1 -signr_addb.
  by rewrite signr_eq0.
have neq_bc: b != c.
  have: phi 1%g == 0 by rewrite (supportP phi1_0) // !inE eqxx.
  rewrite def_phi def_chi def_xi; apply: contraTneq => ->.
  rewrite -scaler_addr !cfunE mulf_eq0 signr_eq0 eqC_leC ltC_geF //.
  by rewrite sposC_addl ?ltCW ?ltC_irr1.
rewrite {}def_phi {}def_chi {}def_xi !scaler_sign.
case: b c neq_bc => [|] [|] // _; last by exists i, j.
by exists j, i; rewrite 1?eq_sym // addrC.
Qed.

End IsVChar.

Section MoreIsVChar.

Variables (gT : finGroupType) (G H : {group gT}).

Lemma vchar_Res A phi : 
  phi \in 'Z[irr G, A] -> 'Res[H] phi \in 'Z[irr H, A].
Proof.
rewrite [phi \in _]vchar_split => /andP[/vcharP[xi1 Nx1 [xi2 Nxi2 ->]] Aphi].
case sHG: (H \subset G); last first.
  congr (_ \in 'Z[_, A]): (vchar0 (irr H) A).
  by apply/cfun_inP=> x Hx; rewrite !cfunElock !genGid Hx sHG.
rewrite vchar_split; apply/andP; split.
  by rewrite linear_sub vchar_sub // vchar_char // is_char_Res.
by apply/supportP=> x /(supportP Aphi); rewrite !cfunElock => ->; exact: mul0rn.
Qed.

Lemma vchar_Ind phi : phi \in 'Z[irr H] -> 'Ind[G, H] phi \in 'Z[irr G].
Proof.
move=> /vcharP[xi1 Nx1 [xi2 Nxi2 ->]].
case sHG: (H \subset G); last first.
  congr (_ \in 'Z[_]): (vchar0 (irr G) setT).
  by apply/cfunP=> x; rewrite !cfunElock !genGid sHG.
by rewrite linear_sub vchar_sub // vchar_char // is_char_Ind.
Qed.

End MoreIsVChar.
