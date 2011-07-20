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
  [pred phi \in span S | [&&  phi \in 'CF(B, A), (phi == 0) || free S
      & coord (in_tuple S) phi \in ffun_on [pred z | isIntC z]]].

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
rewrite 2!inE irr_free cfun_onT tvalK /tcast; case: _ / (esym _).
have /andP[/(span _ =P _)-> _] := irr_is_basis G; rewrite memvf orbT /=.
apply: (iffP ffun_onP) => [Zphi | [chi1 Nchi1 [chi2 Nchi2 ->]] i]; last first.
  rewrite linear_sub !ffunE !coord_cfdot inE /=.
  by rewrite isIntC_add ?isIntC_opp // isIntCE cfdot_char_irr_Nat.
pose Nphi i := isNatC '[phi, 'chi_i].
rewrite [phi]cfun_sum_cfdot (bigID Nphi) /= -[rh in _ + rh]opprK -sumr_opp.
set chi1 := \sum_(i | _) _; set chi2 := \sum_(i | _) _; exists chi1.
  by apply: sum_char => i /scale_char-> //; exact: irr_char.
exists chi2 => //; apply: sum_char => i /negbTE notNphi_i.
rewrite -scaleNr scale_char ?irr_char //.
by have:= Zphi i; rewrite coord_cfdot inE /= isIntCE [isNatC _]notNphi_i.
Qed.

Lemma char_vchar chi : is_char chi -> chi \in 'Z[irr G].
Proof.
move=> Nchi; apply/vcharP; exists chi => //.
by exists 0; rewrite ?cfun0_char ?subr0.
Qed.

Lemma irr_vchar i : 'chi[G]_i \in 'Z[irr G].
Proof. by apply: char_vchar; apply: irr_char. Qed.

Lemma cfun1_vchar : 1 \in 'Z[irr G].
Proof. by rewrite char_vchar ?cfun1_char. Qed.

Lemma vchar_split S A phi :
  phi \in 'Z[S, A] = (phi \in 'Z[S]) && (phi \in 'CF(G, A)).
Proof. by rewrite !inE cfun_onT /= -!andbA; do !bool_congr. Qed.

Lemma vcharD1E phi S : (phi \in 'Z[S, G^#]) = (phi \in 'Z[S]) && (phi 1%g == 0).
Proof. by rewrite vchar_split cfunD1E. Qed.

Lemma vchar_span S A : {subset 'Z[S, A] <= span S}.
Proof. by move=> phi /andP[]. Qed.

Lemma vcharW S A : {subset 'Z[S, A] <= 'Z[S]}.
Proof. by move=> phi; rewrite vchar_split => /andP[]. Qed.

Lemma vchar_on S A : {subset 'Z[S, A] <= 'CF(G, A)}.
Proof. by move=> phi /and3P[]. Qed.

Lemma irr_vchar_on A : {subset 'Z[irr G, A] <= 'CF(G, A)}.
Proof. exact: vchar_on. Qed.

Lemma support_vchar S A phi : phi \in 'Z[S, A] -> support phi \subset A.
Proof. by move/vchar_on; rewrite cfun_onE. Qed.

Lemma mem_vchar_on S A phi : 
  free S -> phi \in 'CF(G, A) -> phi \in S -> phi \in 'Z[S, A].
Proof.
move=> freeS Aphi Sphi; rewrite inE /= freeS orbT Aphi memv_span //=.
have lt_phi_S: (index phi S < size S)%N by rewrite index_mem.
apply/ffun_onP=> i; rewrite inE /=.
by rewrite -(nth_index 0 Sphi) (free_coordt (Ordinal _)) ?isIntC_nat.
Qed.

(* A special lemma is needed because trivial fails to use the cfun_onT Hint. *) 
Lemma mem_vchar S phi : free S -> phi \in S -> phi \in 'Z[S].
Proof. by move=> freeS Sphi; rewrite mem_vchar_on ?cfun_onT. Qed.

Lemma vchar_expansion S A phi :
    phi \in 'Z[S, A] ->
  {z | forall a, isIntC (z a) & phi = \sum_(a <- S) z a *: a}.
Proof.
case/and4P=> Sphi _; case: eqP => [-> _| _ freeS] Zphi.
  exists (fun _ => 0) => [a | ]; first exact: (isIntC_nat 0).
  by rewrite ?big1 // => a; rewrite scale0r.
exists (fun a => oapp (coord (in_tuple S) phi) 0 (insub (index a S))) => [a|].
  by case: insubP => [i|]; rewrite [isIntC _](isIntC_nat 0, ffun_onP Zphi).
rewrite big_tnth {1}[phi](@coord_span _ _ _ (in_tuple S)) //.
by apply: eq_bigr => i _; rewrite (tnth_nth 0) index_uniq ?uniq_free // valK.
Qed.

Lemma irr_orthonormal : orthonormal (irr G).
Proof.
apply/orthonormalP; split; first exact: uniq_free (irr_free G).
move=> _ _ /irrP[i ->] /irrP[j ->].
by rewrite cfdot_irr (inj_eq (@chi_inj _ G)).
Qed.

Lemma coord_vchar_Int m (S : m.-tuple _) A phi i : 
  phi \in 'Z[S, A] -> isIntC (coord S phi i).
Proof.
by case/and4P=> _ _ _ /ffun_onP; rewrite tvalK; case: _ / (esym _); exact.
Qed.

Lemma cfdot_vchar_irr_Int i phi : phi \in 'Z[irr G] -> isIntC '[phi, 'chi_i].
Proof. by rewrite -coord_cfdot => /coord_vchar_Int->. Qed.

Lemma cfdot_vchar_r phi psi :
  psi \in 'Z[irr G] -> '[phi, psi] = \sum_i '[phi, 'chi_i] * '[psi, 'chi_i].
Proof.
move=> VCpsi; rewrite cfdot_sum_irr; apply: eq_bigr => i _; congr (_ * _).
by rewrite isIntC_conj ?cfdot_vchar_irr_Int.
Qed.

Lemma cfdot_vchar_Int : {in 'Z[irr G] &, forall phi psi, isIntC '[phi, psi]}.
Proof.
move=> phi psi Zphi Zpsi; rewrite /= cfdot_vchar_r // isIntC_sum // => k _.
by rewrite isIntC_mul ?cfdot_vchar_irr_Int.
Qed.

Lemma cfnorm_vchar_Nat : {in 'Z[irr G], forall phi, isNatC '[phi]}.
Proof.
by move=> phi Zphi; rewrite /= isNatC_posInt cfnorm_posC cfdot_vchar_Int.
Qed.

Lemma cfun0_vchar S A : 0 \in 'Z[S, A].
Proof.
rewrite !inE eqxx !mem0v /= linear0.
by apply/ffun_onP=> i; rewrite ffunE !inE (isIntC_nat 0).
Qed.

Lemma opp_vchar S A phi : (- phi \in 'Z[S, A]) = (phi \in 'Z[S, A]).
Proof.
rewrite !inE oppr_eq0 !memvN linearN; congr [&& _, _, _ & _].
by apply: eq_forallb => i; rewrite !inE ffunE isIntC_opp.
Qed.

Lemma add_vchar S A phi psi :
  phi \in 'Z[S, A] -> psi \in 'Z[S, A] -> (phi + psi) \in 'Z[S, A].
Proof.
case/and4P=> Sphi Aphi /predU1P[-> | freeS] Zphi; first by rewrite add0r.
case/and4P=> Spsi Apsi _ Zpsi; rewrite !inE freeS orbT !memvD //=.
apply/ffun_onP=> i; rewrite linearD ffunE !inE.
by rewrite !isIntC_add // [isIntC _](ffun_onP Zphi, ffun_onP Zpsi). 
Qed.

Lemma sub_vchar S A phi psi : 
   phi \in 'Z[S, A] -> psi \in 'Z[S, A] -> (phi - psi) \in 'Z[S, A]. 
Proof. by move=> Zphi Zpsi; rewrite add_vchar ?opp_vchar. Qed.

Lemma muln_vchar S A phi n : phi \in 'Z[S, A] -> (phi *+ n) \in 'Z[S, A].
Proof.
by move=> ZSphi; elim: n => [|n Hn]; rewrite ?cfun0_vchar // mulrS add_vchar.
Qed.

Lemma sign_vchar S A phi n :
  ((-1) ^+ n *: phi \in 'Z[S, A]) = (phi \in 'Z[S, A]).
Proof. by rewrite -signr_odd scaler_sign; case: ifP; rewrite ?opp_vchar. Qed.

Lemma scale_vchar S A phi a :
  isIntC a -> phi \in 'Z[S, A] -> a *: phi \in 'Z[S, A].
Proof.
move/eqP=> -> /muln_vchar ZSphi.
by case: getIntC => [b n]; rewrite -scalerA sign_vchar scaler_nat ZSphi.
Qed.

Lemma sum_vchar S A I r (P : pred I) F :
  (forall i, P i -> F i \in 'Z[S, A]) -> \sum_(i <- r | P i) F i \in 'Z[S, A].
Proof.
move=> ZS_F; elim/big_rec: _ => [|i phi Pi ZSphi]; first exact: cfun0_vchar.
by rewrite add_vchar ?ZS_F.
Qed.

Lemma mul_vchar phi psi A : 
  phi \in 'Z[irr G, A]-> psi \in 'Z[irr G, A]-> phi * psi \in 'Z[irr G, A].
Proof.
rewrite !(vchar_split _ A) => /andP[/vcharP[xi1 Nxi1 [xi2 Nxi2 def_phi]] Aphi].
case/andP=> [/vcharP[xi3 Cxi3 [xi4 Nxi4 ->]] _].
apply/andP; split; last first.
  by apply/cfun_onP=> a notAa; rewrite cfunE (cfun_onP Aphi) ?mul0r.
have isch := (add_char, mul_char); apply/vcharP.
exists (xi1 * xi3 + xi2 * xi4); first by rewrite !isch.
exists (xi1 * xi4 + xi2 * xi3); first by rewrite !isch.
by rewrite mulr_subr def_phi !mulr_subl addrAC oppr_sub -!addrA -oppr_add.
Qed.

Lemma vchar_trans S1 S2 A B :
  {subset S1 <= 'Z[S2, B]} -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> sS12 phi; rewrite !(vchar_split _ A) andbC => /andP[->].
case/vchar_expansion=> z Zz ->; rewrite big_seq sum_vchar // => a S1a.
by rewrite scale_vchar //; exact: vcharW (sS12 a S1a).
Qed.

Lemma vchar_trans_on S1 S2 A :
  {subset S1 <= 'Z[S2, A]} -> {subset 'Z[S1] <= 'Z[S2, A]}.
Proof.
move=> sS12 _ /vchar_expansion[z Zz ->].
rewrite big_seq sum_vchar // => phi /sS12; exact: scale_vchar.
Qed.

Lemma vchar_sub_irr S A :
  {subset S <= 'Z[irr G]} -> {subset 'Z[S, A] <= 'Z[irr G, A]}.
Proof. exact: vchar_trans. Qed.

Lemma vchar_subset S1 S2 A :
  free S2 -> {subset S1 <= S2} -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS2 sS12; apply: vchar_trans setT _ => // f /sS12 S2f.
by rewrite mem_vchar.
Qed.

Lemma vchar_subseq S1 S2 A :
  free S2 -> subseq S1 S2 -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof. move=> freeS2 sS12; exact: vchar_subset (mem_subseq sS12). Qed.

Lemma vchar_filter S A (p : pred 'CF(G)) :
  free S -> {subset 'Z[filter p S, A] <= 'Z[S, A]}.
Proof. by move/vchar_subset; apply=> f; rewrite mem_filter => /andP[]. Qed.

Lemma vchar_orthonormalP (S : seq 'CF(G)) :
    {subset S <= 'Z[irr G]} ->
  reflect (exists I : {set Iirr G}, exists b : Iirr G -> bool,
           perm_eq S [seq (-1) ^+ b i *: 'chi_i | i <- enum I])
          (orthonormal S).
Proof.
move=> vcS; apply: (equivP orthonormalP).
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
  by rewrite -normCK ?isNatC_mul ?normIntC_Nat ?cfdot_vchar_irr_Int.
suffices def_xi: xi = (-1) ^+ b i *: 'chi_i.
  exists i; rewrite // mem_enum inE -/(b i) orbC.
  by case: (b i) def_xi Sxi => // ->; rewrite scale1r.
move: Sxi; rewrite [xi]cfun_sum_cfdot (bigD1 i) //.
rewrite big1 //= ?addr0 => [|j ne_ji]; last first.
  apply/eqP; rewrite scalev_eq0 -normC_eq0 -[_ == 0](expf_eq0 _ 2) normCK.
  by rewrite xi_i'_0 ?eqxx.
have:= norm_xi_i; rewrite (isIntC_conj (cfdot_vchar_irr_Int _ _)) //.
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
pose S := [image '[phi, 'chi_i] *: 'chi_i | i <- irr_constt phi].
have def_phi: phi = \sum_(xi <- S) xi.
  rewrite big_map /= big_filter big_mkcond {1}[phi]cfun_sum_cfdot.
  by apply: eq_bigr => i _; rewrite if_neg; case: eqP => // ->; rewrite scale0r.
have orthS: orthonormal S.
  apply/orthonormalP; split=> [|_ _ /mapP[i phi_i ->] /mapP[j _ ->]].
    rewrite map_inj_in_uniq ?enum_uniq // => i j; rewrite mem_enum => phi_i _.
    by move/eqP; rewrite eq_scaled_irr (negbTE phi_i) => /andP[_ /= /eqP].
  rewrite eq_scaled_irr cfdotZl cfdotZr cfdot_irr mulrA mulr_natr mulrb.
  rewrite mem_enum in phi_i; rewrite (negbTE phi_i) andbC; case: eqP => // <-.
  have /isNatCP[m def_m] := normIntC_Nat (cfdot_vchar_irr_Int i Zphi).
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
by rewrite scale_vchar ?irr_vchar // cfdot_vchar_irr_Int.
Qed.

Lemma vchar_norm2 phi :
    phi \in 'Z[irr G, G^#] -> '[phi] = 2%:R ->
  exists i, exists2 j, j != i & phi = 'chi_i - 'chi_j.
Proof.
rewrite vchar_split cfunD1E => /andP[Zphi phi1_0].
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
  apply: contraTneq phi1_0; rewrite def_phi def_chi def_xi => ->.
  rewrite -scaler_addr !cfunE mulf_eq0 signr_eq0 eqC_leC ltC_geF //.
  by rewrite sposC_addl ?ltCW ?ltC_irr1.
rewrite {}def_phi {}def_chi {}def_xi !scaler_sign.
case: b c neq_bc => [|] [|] // _; last by exists i, j.
by exists j, i; rewrite 1?eq_sym // addrC.
Qed.

End IsVChar.

Section Isometries.

Variables (gT : finGroupType) (L G : {group gT}).
Implicit Types (S : seq 'CF(L)).

Lemma Zisometry_of_cfnorm S tauS :
    pairwise_orthogonal S -> pairwise_orthogonal tauS ->
    map cfnorm tauS = map cfnorm S -> {subset tauS <= 'Z[irr G]} ->
  {tau : {linear 'CF(L) -> 'CF(G)} | map tau S = tauS
       & {in 'Z[S], isometry tau, to 'Z[irr G]}}.
Proof.
move=> oS oT eq_nTS Z_T.
have [tau defT Itau] := isometry_of_cfnorm oS oT eq_nTS.
exists tau => //; split; first exact: (sub_in2 (@vchar_span _ _ S _)).
move=> _ /vchar_expansion[z Zz ->].
rewrite big_seq linear_sum sum_vchar // => xi Sxi.
by rewrite linearZ scale_vchar ?Z_T // -defT map_f.
Qed.

Lemma Zisometry_inj S A (tau : {additive 'CF(L) -> 'CF(G)}) :
    {in 'Z[S, A] &, isometry tau} -> {in 'Z[S, A] &, injective tau}.
Proof. by move/isometry_inj; apply; exact: sub_vchar. Qed.

Lemma map_pairwise_orthogonal S (tau : {additive 'CF(L) -> 'CF(G)}) :
    {in 'Z[S] &, isometry tau} ->
  pairwise_orthogonal S -> pairwise_orthogonal (map tau S).
Proof.
move=> Itau oS; have freeS := orthogonal_free oS.
apply/pairwise_orthogonalP; have{oS} [uS oS] := pairwise_orthogonalP oS.
have inj_tau: {in 0 :: S &, injective tau}.
  apply: sub_in2 (Zisometry_inj Itau) => xi.
  by case/predU1P=> [-> | /mem_vchar->]; rewrite ?cfun0_vchar.
split; first by rewrite -(map_inj_in_uniq inj_tau) /= raddf0 in uS.
move=> _ _ /mapP[xi1 S1xi1 ->] /mapP[xi2 S1xi2 ->] neq_tau_xi.
by rewrite Itau ?mem_vchar ?oS //; apply: contraNneq neq_tau_xi => ->.
Qed.

Lemma map_orthonormal S (tau : {additive 'CF(L) -> 'CF(G)}) :
  {in 'Z[S] &, isometry tau} -> orthonormal S -> orthonormal (map tau S).
Proof.
move=> Itau1 /andP[/allP/=nS oS]; have freeS := orthogonal_free oS.
apply/andP; split; last exact: map_pairwise_orthogonal.
by apply/allP=> _ /mapP[xi S1xi -> /=]; rewrite Itau1 ?mem_vchar ?nS.
Qed.

End Isometries.

Section MoreIsVChar.

Variables (gT : finGroupType) (G H : {group gT}).

Lemma cfRes_vchar A phi : 
  phi \in 'Z[irr G, A] -> 'Res[H] phi \in 'Z[irr H, A].
Proof.
rewrite [phi \in _]vchar_split => /andP[/vcharP[xi1 Nx1 [xi2 Nxi2 ->]] Aphi].
case sHG: (H \subset G); last first.
  congr (_ \in 'Z[_, A]): (cfun0_vchar (irr H) A).
  by apply/cfun_inP=> x Hx; rewrite !cfunElock !genGid Hx sHG.
rewrite vchar_split; apply/andP; split.
  by rewrite linear_sub sub_vchar // char_vchar // cfRes_char.
by apply/cfun_onP=> x /(cfun_onP Aphi); rewrite !cfunElock => ->; exact: mul0rn.
Qed.

Lemma cfInd_vchar phi : phi \in 'Z[irr H] -> 'Ind[G, H] phi \in 'Z[irr G].
Proof.
move=> /vcharP[xi1 Nx1 [xi2 Nxi2 ->]].
case sHG: (H \subset G); last first.
  congr (_ \in 'Z[_]): (cfun0_vchar (irr G) setT).
  by apply/cfunP=> x; rewrite !cfunElock !genGid sHG.
by rewrite linear_sub sub_vchar // char_vchar // cfInd_char.
Qed.

(* to do: cfAut, etc. *)

End MoreIsVChar.
