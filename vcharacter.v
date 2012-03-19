(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import gproduct zmodp commutator cyclic center pgroup sylow frobenius.
Require Import vector algC classfun character.

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
  [pred phi \in <<S>>%VS | [&& phi \in 'CF(B, A), (phi == 0) || free S
      & forallb i, isIntC (coord (in_tuple S) i phi)]].

Notation "''Z[' S , A ]" := (virtual_char S A)
  (at level 8, format "''Z[' S ,  A ]") : group_scope. 
Notation "''Z[' S ]" := 'Z[S, setT]
  (at level 8, format "''Z[' S ]") : group_scope.

Section IsVChar.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types (A : {set gT}) (phi chi : 'CF(G)) (S : seq 'CF(G)).

Lemma vcharP phi :
  reflect (exists2 chi1, is_char chi1 & exists2 chi2, is_char chi2
                       & phi = chi1 - chi2)
          (phi \in 'Z[irr G]).
Proof.
rewrite inE irr_free cfun_onT tvalK /tcast; case: _ / (esym _).
have /andP[/(<<_>>%VS =P _)-> _] := irr_basis G; rewrite memvf orbT /=.
apply: (iffP forallP) => [Zphi | [chi1 Nchi1 [chi2 Nchi2 ->]] i]; last first.
  rewrite linearB /= !coord_cfdot.
  by rewrite isIntC_add ?isIntC_opp // isIntCE cfdot_char_irr_Nat.
pose Nphi i := isNatC '[phi, 'chi_i].
rewrite [phi]cfun_sum_cfdot (bigID Nphi) /= -[rh in _ + rh]opprK -sumrN.
set chi1 := \sum_(i | _) _; set chi2 := \sum_(i | _) _; exists chi1.
  by apply: sum_char => i /scale_char-> //; exact: irr_char.
exists chi2 => //; apply: sum_char => i /negbTE notNphi_i.
rewrite -scaleNr scale_char ?irr_char //.
by have:= Zphi i; rewrite coord_cfdot /= isIntCE [isNatC _]notNphi_i.
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

Lemma vchar1_Int phi : phi \in 'Z[irr G] -> isIntC (phi 1%g).
Proof.
case/vcharP=> phi1 Nphi1 [phi2 Nphi2 ->].
by rewrite !cfunE isIntC_add // isIntCE ?opprK char1_Nat ?orbT.
Qed.

Lemma vchar_split S A phi :
  phi \in 'Z[S, A] = (phi \in 'Z[S]) && (phi \in 'CF(G, A)).
Proof. by rewrite !inE cfun_onT /= -!andbA; do !bool_congr. Qed.

Lemma vcharD1E phi S : (phi \in 'Z[S, G^#]) = (phi \in 'Z[S]) && (phi 1%g == 0).
Proof. by rewrite vchar_split cfunD1E. Qed.

Lemma vcharD1 phi S A :
  (phi \in 'Z[S, A^#]) = (phi \in 'Z[S, A]) && (phi 1%g == 0).
Proof. by rewrite vchar_split cfun_onD1 andbA -vchar_split. Qed.

Lemma vchar_span S A : {subset 'Z[S, A] <= <<S>>%VS}.
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
apply/forallP=> i.
by rewrite -(nth_index 0 Sphi) (coord_free (Ordinal _)) ?isIntC_nat.
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
exists (fun a => oapp ((coord (in_tuple S))^~ phi) 0 (insub (index a S))).
  by move=> a; case: insubP => [i|] /= _; rewrite (isIntC_nat 0, forallP Zphi).
rewrite big_tnth {1}[phi](@coord_span _ _ _ (in_tuple S)) //.
by apply: eq_bigr => i _; rewrite (tnth_nth 0) index_uniq ?free_uniq // valK.
Qed.

Lemma irr_orthonormal : orthonormal (irr G).
Proof.
apply/orthonormalP; split; first exact: free_uniq (irr_free G).
move=> _ _ /irrP[i ->] /irrP[j ->].
by rewrite cfdot_irr (inj_eq (@chi_inj _ G)).
Qed.

Lemma coord_vchar_Int m (S : m.-tuple _) A phi i : 
  phi \in 'Z[S, A] -> isIntC (coord S i phi).
Proof.
by case/and4P=> _ _ _ /forallP; rewrite tvalK; case: _ / (esym _); exact.
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
by rewrite !inE eqxx !mem0v; apply/forallP=> i; rewrite linear0 (isIntC_nat 0).
Qed.

Lemma opp_vchar S A phi : (- phi \in 'Z[S, A]) = (phi \in 'Z[S, A]).
Proof.
rewrite !inE oppr_eq0 !memvN /=; congr [&& _, _, _ & _].
by apply: eq_forallb => i; rewrite linearN isIntC_opp.
Qed.

Lemma add_vchar S A phi psi :
  phi \in 'Z[S, A] -> psi \in 'Z[S, A] -> (phi + psi) \in 'Z[S, A].
Proof.
case/and4P=> Sphi Aphi /predU1P[-> | freeS] Zphi; first by rewrite add0r.
case/and4P=> Spsi Apsi _ Zpsi; rewrite !inE freeS orbT !memvD //=.
by apply/forallP=> i; rewrite linearD isIntC_add ?(forallP Zphi, forallP Zpsi). 
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
by rewrite mulrBr def_phi !mulrBl addrAC opprB -!addrA -opprD.
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

Section CfdotPairwiseOrthogonal.

Variables (M : {group gT}) (S : seq 'CF(G)) (nu : 'CF(G) -> 'CF(M)).
Hypotheses (Inu : {in 'Z[S] &, isometry nu}) (oSS : pairwise_orthogonal S).

Let freeS := orthogonal_free oSS.
Let uniqS : uniq S := free_uniq freeS.
Let Z_S : {subset S <= 'Z[S]}. Proof. by move=> phi; exact: mem_vchar. Qed.
Let notS0 : 0 \notin S. Proof. by case/andP: oSS. Qed.
Let dotSS := proj2 (pairwise_orthogonalP oSS).

Lemma map_pairwise_orthogonal : pairwise_orthogonal (map nu S).
Proof.
have inj_nu: {in S &, injective nu}.
  move=> phi psi Sphi Spsi /= eq_nu; apply: contraNeq (memPn notS0 _ Sphi).
  by rewrite -cfnorm_eq0 -Inu ?Z_S // {2}eq_nu Inu ?Z_S // => /dotSS->.
have notSnu0: 0 \notin map nu S.
  apply: contra notS0 => /mapP[phi Sphi /esym/eqP].
  by rewrite -cfnorm_eq0 Inu ?Z_S // cfnorm_eq0 => /eqP <-.
apply/pairwise_orthogonalP; split; first by rewrite /= notSnu0 map_inj_in_uniq.
move=>_ _ /mapP[phi Sphi ->] /mapP[psi Spsi ->].
by rewrite (inj_in_eq inj_nu) // Inu ?Z_S //; exact: dotSS.
Qed.

Lemma cfproj_sum_orthogonal P z phi :
    phi \in S ->
  '[\sum_(xi <- S | P xi) z xi *: nu xi, nu phi]
    = if P phi then z phi * '[phi] else 0.
Proof.
move=> Sphi; have defS := perm_to_rem Sphi.
rewrite cfdot_suml (eq_big_perm _ defS) big_cons /= cfdotZl Inu ?Z_S //.
rewrite big1_seq ?addr0 // => xi; rewrite mem_rem_uniq ?inE //.
by case/and3P=> _ neq_xi Sxi; rewrite cfdotZl Inu ?Z_S // dotSS ?mulr0.
Qed.

Lemma cfdot_sum_orthogonal z1 z2 :
  '[\sum_(xi <- S) z1 xi *: nu xi, \sum_(xi <- S) z2 xi *: nu xi]
    = \sum_(xi <- S) z1 xi * (z2 xi)^* * '[xi].
Proof.
rewrite cfdot_sumr; apply: eq_big_seq => phi Sphi.
by rewrite cfdotZr cfproj_sum_orthogonal // mulrCA mulrA.
Qed.

Lemma cfnorm_sum_orthogonal z :
  '[\sum_(xi <- S) z xi *: nu xi] = \sum_(xi <- S) `|z xi| ^+ 2 * '[xi].
Proof.
by rewrite cfdot_sum_orthogonal; apply: eq_bigr => xi _; rewrite normCK.
Qed.

Lemma cfnorm_orthogonal : '[\sum_(xi <- S) nu xi] = \sum_(xi <- S) '[xi].
Proof.
rewrite -(eq_bigr _ (fun _ _ => scale1r _)) cfnorm_sum_orthogonal.
by apply: eq_bigr => xi; rewrite normCK conjC1 !mul1r.
Qed.

End CfdotPairwiseOrthogonal.

Lemma orthogonal_span S phi :
    pairwise_orthogonal S -> phi \in <<S>>%VS ->
  {z | z = fun xi => '[phi, xi] / '[xi] & phi = \sum_(xi <- S) z xi *: xi}.
Proof.
move=> oSS /free_span[|c -> _]; first exact: orthogonal_free.
set z := fun _ => _ : algC; exists z => //; apply: eq_big_seq => u Su.
rewrite /z cfproj_sum_orthogonal // mulfK // cfnorm_eq0.
by rewrite (memPn _ u Su); case/andP: oSS.
Qed.

Section CfDotOrthonormal.

Variables (M : {group gT}) (S : seq 'CF(G)) (nu : 'CF(G) -> 'CF(M)).
Hypotheses (Inu : {in 'Z[S] &, isometry nu}) (onS : orthonormal S).
Let oSS := orthonormal_orthogonal onS.
Let nS1 : {in S, forall phi, '[phi] = 1}.
Proof. by move=> phi Sphi; case/orthonormalP: onS => _ -> //; rewrite eqxx. Qed.

Lemma cfproj_sum_orthonormal z phi :
  phi \in S -> '[\sum_(xi <- S) z xi *: nu xi, nu phi] = z phi.
Proof. by move=> Sphi; rewrite cfproj_sum_orthogonal // nS1 // mulr1. Qed.

Lemma cfdot_sum_orthonormal z1 z2 :
  '[\sum_(xi <- S) z1 xi *: xi, \sum_(xi <- S) z2 xi *: xi]
     = \sum_(xi <- S) z1 xi * (z2 xi)^*.
Proof.
rewrite cfdot_sum_orthogonal //; apply: eq_big_seq => phi /nS1->.
by rewrite mulr1.
Qed.

Lemma cfnorm_sum_orthonormal z :
  '[\sum_(xi <- S) z xi *: nu xi] = \sum_(xi <- S) `|z xi| ^+ 2.
Proof.
rewrite cfnorm_sum_orthogonal //.
by apply: eq_big_seq => xi /nS1->; rewrite mulr1.
Qed.

Lemma cfnorm_map_orthonormal : '[\sum_(xi <- S) nu xi] = (size S)%:R.
Proof.
by rewrite cfnorm_orthogonal // (eq_big_seq _ nS1) big_tnth sumr_const card_ord.
Qed.

Lemma orthonormal_span phi :
    phi \in <<S>>%VS ->
  {z | z = fun xi => '[phi, xi] & phi = \sum_(xi <- S) z xi *: xi}.
Proof.
case/orthogonal_span=> // _ -> {2}->; set z := fun _ => _ : algC.
by exists z => //; apply: eq_big_seq => xi /nS1->; rewrite divr1.
Qed.

End CfDotOrthonormal.

Lemma cfnorm_orthonormal S :
  orthonormal S -> '[\sum_(xi <- S) xi] = (size S)%:R.
Proof. exact: cfnorm_map_orthonormal. Qed.

Lemma vchar_orthonormalP S :
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
  apply/eqP; rewrite scaler_eq0 -normC_eq0 -[_ == 0](expf_eq0 _ 2) normCK.
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
have: orthonormal phi by rewrite /orthonormal/= phiN1 eqxx.
case/vchar_orthonormalP=> [xi /predU1P[->|] // | I [b def_phi]].
have: phi \in (phi : seq _) := mem_head _ _.
by rewrite (perm_eq_mem def_phi) => /mapP[i _ ->]; exists (b i), i.
Qed.

Lemma vchar_small_norm phi n :
    phi \in 'Z[irr G] -> '[phi] = n%:R -> (n < 4)%N ->
  {S : n.-tuple 'CF(G) |
    [/\ orthonormal S, {subset S <= 'Z[irr G]} & phi = \sum_(xi <- S) xi]}.
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
  apply/eqP; rewrite eqxx /= -normCK def_m -natrX -eqN_eqC eqn_leq lt0n.
  rewrite expn_eq0 andbT eqN_eqC -def_m normC_eq0 [~~ _]phi_i andbT.
  rewrite (leq_exp2r _ 1) // -ltnS -(@ltn_exp2r _ _ 2) //.
  apply: leq_ltn_trans lt_n_4; rewrite leq_leC -def_n natrX.
  rewrite cfdot_sum_irr (bigD1 i) //= -normCK def_m addrC -leC_sub addrK.
  by rewrite posC_sum // => ? _; exact: posC_pconj.
have <-: size S = n.
  by apply/eqP; rewrite eqN_eqC -def_n def_phi cfnorm_orthonormal.
exists (in_tuple S); split=> // _ /mapP[i _ ->].
by rewrite scale_vchar ?irr_vchar // cfdot_vchar_irr_Int.
Qed.

Lemma vchar_norm2 phi :
    phi \in 'Z[irr G, G^#] -> '[phi] = 2%:R ->
  exists i, exists2 j, j != i & phi = 'chi_i - 'chi_j.
Proof.
rewrite vchar_split cfunD1E => /andP[Zphi phi1_0].
case/vchar_small_norm => // [[[|chi [|xi [|?]]] //= S2]].
case=> /andP[/and3P[Nchi Nxi _] /= ochi] /allP/and3P[Zchi Zxi _].
rewrite big_cons big_seq1 => def_phi.
have [b [i def_chi]] := vchar_norm1P Zchi (eqP Nchi).
have [c [j def_xi]] := vchar_norm1P Zxi (eqP Nxi).
have neq_ji: j != i.
  apply: contraTneq ochi; rewrite !andbT def_chi def_xi => ->.
  rewrite cfdotZl cfdotZr rmorph_sign cfnorm_irr mulr1 -signr_addb.
  by rewrite signr_eq0.
have neq_bc: b != c.
  apply: contraTneq phi1_0; rewrite def_phi def_chi def_xi => ->.
  rewrite -scalerDr !cfunE mulf_eq0 signr_eq0 eqC_leC ltC_geF //.
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
Proof. by move/isometry_raddf_inj; apply; exact: sub_vchar. Qed.

End Isometries.

Section AutVchar.

Variables (u : {rmorphism algC -> algC}) (gT : finGroupType) (G : {group gT}).
Local Notation "alpha ^u" := (cfAut u alpha).
Implicit Type S : seq 'CF(G).

Lemma cfAut_vchar S A psi : 
  free S -> cfAut_closed u S -> psi \in 'Z[S, A] -> psi^u \in 'Z[S, A].
Proof.
rewrite [psi \in _]vchar_split => freeS SuS /andP[Zpsi Apsi].
rewrite vchar_split cfAut_on {}Apsi andbT.
have{psi Zpsi}[z Zz ->] := vchar_expansion Zpsi.
rewrite rmorph_sum big_seq sum_vchar // => mu Smu /=.
by rewrite cfAutZ_Int // scale_vchar // mem_vchar // SuS.
Qed.

Lemma cfAut_virr A psi : psi \in 'Z[irr G, A] -> psi^u \in 'Z[irr G, A].
Proof. by apply: cfAut_vchar; [exact: irr_free | exact: irr_Aut_closed]. Qed.

Lemma sub_Aut_vchar S A psi :
   {subset S <= 'Z[irr G]} -> psi \in 'Z[S, A] -> psi^u \in 'Z[S, A] ->
  psi - psi^u \in 'Z[S, A^#].
Proof.
move=> Z_S Spsi Spsi_u; rewrite vcharD1 !cfunE subr_eq0 sub_vchar //=.
by rewrite rmorph_IntC // vchar1_Int // (vchar_trans Z_S) ?(vcharW Spsi).
Qed.

End AutVchar.

Definition cfConjC_virr :=  cfAut_virr conjC.

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
  by rewrite linearB sub_vchar // char_vchar // cfRes_char.
by apply/cfun_onP=> x /(cfun_onP Aphi); rewrite !cfunElock => ->; exact: mul0rn.
Qed.

Lemma cfInd_vchar phi : phi \in 'Z[irr H] -> 'Ind[G] phi \in 'Z[irr G].
Proof.
move=> /vcharP[xi1 Nx1 [xi2 Nxi2 ->]].
case sHG: (H \subset G); last first.
  congr (_ \in 'Z[_]): (cfun0_vchar (irr G) setT).
  by apply/cfunP=> x; rewrite !cfunElock !genGid sHG.
by rewrite linearB sub_vchar // char_vchar // cfInd_char.
Qed.

Lemma sub_conjC_vchar A phi :
  phi \in 'Z[irr G, A] -> phi - (phi^*)%CF \in 'Z[irr G, A^#].
Proof.
move=> Zphi; rewrite sub_Aut_vchar ?cfAut_vchar ?irr_free // => _ /irrP[i ->].
  exact: irr_vchar.
exact: cfConjC_irr.
Qed.

Lemma Frobenius_kernel_exists :
  [Frobenius G with complement H] -> {K : {group gT} | [Frobenius G = K ><| H]}.
Proof.
move=> frobG; have [/andP[sHG ltHG] ntiHG] := andP frobG.
have [tiHG /eqP defNH] := andP ntiHG; rewrite -defNH subsetIidl in ltHG.
suffices /sigW[K defG]: exists K, gval K ><| H == G by exists K; exact/andP.
have{ltHG} ntH: H :!=: 1%g by apply: contraNneq ltHG => ->; exact: norms1.
pose K1 := G :\: cover (H^# :^: G).
have oK1:  #|K1| = #|G : H|.
  rewrite cardsD (setIidPr _); last first.
    rewrite cover_imset; apply/bigcupsP=> x Gx.
    by rewrite sub_conjg conjGid ?groupV // (subset_trans (subsetDl _ _)).
  rewrite -(eqnP tiHG) (eq_bigr (fun _ => #|H|.-1)); last first.
    by move=> _ /imsetP[x _ ->]; rewrite cardJg (cardsD1 1%g H) group1.
  rewrite sum_nat_const card_orbit astab1Js normD1 defNH.
  by rewrite -subn1 mulnBr mulnC Lagrange // muln1 subKn ?leq_imset_card.
suffices extG i: {j | {in H, 'chi[G]_j =1 'chi[H]_i} & K1 \subset cfker 'chi_j}.
  pose K := [group of \bigcap_i cfker 'chi_(s2val (extG i))].
  have nKH: H \subset 'N(K).
    by apply/norms_bigcap/bigcapsP=> i _; exact: subset_trans (cfker_norm _).
  have tiKH: K :&: H = 1%g.
    apply/trivgP; rewrite -(TI_cfker_irr H) /= setIC; apply/bigcapsP=> i _.
    apply/subsetP=> x /setIP[Hx /bigcapP/(_ i isT)/=]; rewrite !cfker_irrE !inE.
    by case: (extG i) => /= j def_j _; rewrite !def_j.
  exists K; rewrite sdprodE // eqEcard TI_cardMg // mul_subG //=; last first.
    by rewrite (bigcap_min (0 : Iirr H)) ?cfker_sub.
  rewrite -(Lagrange sHG) mulnC leq_pmul2r // -oK1 subset_leq_card //.
  by apply/bigcapsP=> i _; case: (extG i).
case i0: (i == 0).
  exists 0 => [x Hx|]; last by rewrite chi0_1 cfker_cfun1 subsetDl.
  by rewrite (eqP i0) !chi0_1 !cfun1E // (subsetP sHG) ?Hx.
have ochi1: '['chi_i, 1] = 0 by rewrite -chi0_1 cfdot_irr i0.
pose a := 'chi_i 1%g; have Za: isIntC a by rewrite isIntCE isNatC_irr1.
pose theta := 'chi_i - a%:A; pose phi := 'Ind[G] theta + a%:A.
have /cfun_onP theta0: theta \in 'CF(H, H^#).
  by rewrite cfunD1E !cfunE cfun1E // group1 mulr1 subrr.
have RItheta: 'Res ('Ind[G] theta) = theta.
  apply/cfun_inP=> x Hx; rewrite cfResE ?cfIndE // (big_setID H) /= addrC.
  apply: canLR (mulKf (neq0GC H)) _; rewrite (setIidPr sHG) mulr_natl.
  rewrite big1 ?add0r => [|y /(TIconj_SN_P ntH sHG ntiHG) tiHy]; last first.
    by rewrite theta0 // inE -set1gE -tiHy inE memJ_conjg Hx andbT andNb.
  by rewrite -sumr_const; apply: eq_bigr => y Hy; rewrite cfunJ.
have ophi1: '[phi, 1] = 0.
  rewrite cfdotDl -cfdot_Res_r cfRes_cfun1 // cfdot_subl !cfdotZl !cfnorm1.
  by rewrite ochi1 add0r addNr.
have{ochi1} n1phi: '[phi] = 1.
  have: '[phi - a%:A] = '[theta] by rewrite addrK -cfdot_Res_l RItheta.
  rewrite !cfnorm_subd ?cfnormZ ?cfdotZr ?ophi1 ?ochi1 ?mulr0 //.
  by rewrite !cfnorm1 cfnorm_irr => /addIr.
have Zphi: phi \in 'Z[irr G].
  rewrite ?(cfInd_vchar, sub_vchar, add_vchar, scale_vchar) ?cfun1_vchar //.
  exact: irr_vchar.
have def_phi: {in H, phi =1 'chi_i}.
  move=> x Hx /=; rewrite !cfunE -[_ x](cfResE _ sHG) ?RItheta //.
  by rewrite !cfunE !cfun1E ?(subsetP sHG) ?Hx ?subrK.
have [j def_chi_j]: {j | 'chi_j = phi}.
  apply/sig_eqW; have [[] [j]] := vchar_norm1P Zphi n1phi; last first.
    by rewrite scale1r; exists j.
  move/cfunP/(_ 1%g)/eqP; rewrite scaleN1r def_phi // cfunE -addr_eq0 eqC_leC.
  by rewrite ltC_geF // sposC_addl ?ltCW ?ltC_irr1.
exists j; rewrite ?cfker_irrE def_chi_j //; apply/subsetP => x /setDP[Gx notHx].
rewrite inE cfunE def_phi // cfunE -/a cfun1E // Gx mulr1 cfIndE //.
rewrite big1 ?mulr0 ?add0r // => y Gy; apply/theta0/(contra _ notHx) => Hxy.
by rewrite -(conjgK y x) cover_imset -class_supportEr mem_imset2 ?groupV. 
Qed.

End MoreIsVChar.

