(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import gproduct zmodp commutator cyclic center pgroup sylow frobenius.
Require Import vector algC algnum classfun character integral_char.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file provides basic notions of virtual character theory:              *)
(*       'Z[S, A] == collective predicate for the phi that are Z-linear       *)
(*                   combinations of elements of S : seq 'CF(G) and have      *)
(*                   support in A : {set gT}.                                 *)
(*          'Z[S] == collective predicate for the Z-linear combinations of    *)
(*                   elements of S.                                           *)
(*      'Z[irr G] == the collective predicate for virtual characters.         *)
(*         dirr G == the collective predicate for normal virtual characters,  *)
(*                   i.e., virtual characters of norm 1:                      *)
(*               mu \in dirr G <=> m \in 'Z[irr G] and '[mu] = 1              *)
(*                             <=> mu or - mu \in irr G.                      *)
(* --> othonormal subsets of 'Z[irr G] are contained in dirr G.               *)
(*        dIirr G == an index type for normal virtual characters.             *)
(*         dchi i == the normal virtual character of index i.                 *)
(*       of_irr i == the (unique) irreducible constituent of dchi i:          *)
(*                   dchi i = 'chi_(of_irr i) or - 'chi_(of_irr i).           *)
(*        ndirr i == the index of - dchi i.                                   *)
(*        dirr1 G == the normal virtual character index of 1 : 'CF(G), the    *)
(*                   principal character.                                     *)
(* dirr_dIirr j f == the index i (or dirr1 G if it does not exist) such that  *)
(*                   dchi i = f j.                                            *)
(* dirr_constt phi == the normal virtual character constituents of phi:       *)
(*                    i \in dirr_constt phi <=> [dchi i, phi] > 0.            *)
(*  to_dirr phi i == the normal virtual character constituent of phi with an  *)
(*                   irreducible constituent i, when i \in irr_constt phi.    *)
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
Implicit Types (A B : {set gT}) (phi chi : 'CF(G)) (S : seq 'CF(G)).

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

Lemma algInt_vchar phi x : phi \in 'Z[irr G] -> phi x \in algInt.
Proof.
case/vcharP=> [chi1 Nchi1 [chi2 Nchi2 ->]].
by rewrite !cfunE rpredB ?algInt_char.
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

Lemma vchar_onS A B S : A \subset B -> {subset 'Z[S, A] <= 'Z[S, B]}.
Proof.
move=> sAB phi; rewrite vchar_split (vchar_split _ B) => /andP[->].
exact: cfun_onS.
Qed.

Lemma vchar_onG S : 'Z[S, G] =i 'Z[S].
Proof. by move=> phi; rewrite vchar_split cfun_onG andbT. Qed.

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
Let freeS := orthogonal_free oSS.
Let nS1 : {in S, forall phi, '[phi] = 1}.
Proof. by move=> phi Sphi; case/orthonormalP: onS => _ -> //; rewrite eqxx. Qed.

Lemma map_orthonormal : orthonormal (map nu S).
Proof.
rewrite !orthonormalE map_pairwise_orthogonal // andbT.
by apply/allP=> _ /mapP[xi Sxi ->]; rewrite /= Inu ?nS1 // mem_vchar.
Qed.

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
Implicit Type (S : seq 'CF(G)) (phi chi : 'CF(G)).

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

Lemma conjC_vcharAut chi x : chi \in 'Z[irr G] -> (u (chi x))^* = u (chi x)^*.
Proof.
case/vcharP=> chi1 Nchi1 [chi2 Nchi2 ->].
by rewrite !cfunE !rmorphB !conjC_charAut.
Qed.

Lemma cfdot_cfAut_vchar phi chi :
  chi \in 'Z[irr G] -> '[phi^u , chi^u] = u '[phi, chi].
Proof.
case/vcharP=> chi1 Nchi1 [chi2 Nchi2 ->].
by rewrite !raddfB /= !cfdot_cfAut_char.
Qed.

Lemma vchar_cfAut A chi : (chi^u \in 'Z[irr G, A]) = (chi \in 'Z[irr G, A]).
Proof.
rewrite !(vchar_split _ A) cfAut_on; congr (_ && _).
apply/idP/idP=> [Zuchi|]; last exact: cfAut_virr.
rewrite [chi]cfun_sum_cfdot sum_vchar // => i _.
rewrite scale_vchar ?irr_vchar //.
by rewrite -(isIntC_rmorph u) -cfdot_cfAut_irr -aut_IirrE cfdot_vchar_irr_Int.
Qed.

End AutVchar.

Definition cfConjC_virr :=  cfAut_virr conjC.

Section MoreVchar.

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

End MoreVchar.

Section Norm1vchar.

Variables (gT : finGroupType) (G : {group gT}).

Definition dirr (B : {set gT}) :=  
  [pred f | (f \in irr B) || (-f \in irr B)].

Lemma dirr_opp v : (- v \in dirr G) = (v \in dirr G).
Proof. by rewrite !inE opprK orbC. Qed.

Lemma dirr_sign n v : ((-1)^+ n *: v \in dirr G) = (v \in dirr G).
Proof.
elim: n => [|n IH]; first by rewrite scale1r.
by rewrite exprS -scalerA scaleN1r dirr_opp.
Qed.

Lemma dirr_chi i : 'chi_i \in dirr G.
Proof. by rewrite !inE irr_chi. Qed.

Lemma dirrP f :
  reflect (exists b : bool, exists i, f = (-1) ^+ b *: 'chi_i)
          (f \in dirr G).
Proof.
apply: (iffP idP)=> [| [b [i ->]]]. 
  rewrite inE => /orP [] /irrP [] i Hf.
    by exists false; exists i; rewrite scale1r.
  by exists true; exists i; rewrite expr1 scaleNr scale1r -Hf opprK.
by rewrite dirr_sign dirr_chi.
Qed.

(* This should perhaps be the definition of dirr. *)
Lemma dirrE phi : phi \in dirr G = (phi \in 'Z[irr G]) && ('[phi] == 1).
Proof.
apply/dirrP/andP=> [[b [i ->]] | [Zphi /eqP/vchar_norm1P]]; last exact.
by rewrite sign_vchar irr_vchar cfnorm_sign cfnorm_irr.
Qed.

Lemma cfdot_dirr f g : f \in dirr G -> g \in dirr G ->
  '[f, g] = (if f == - g then -1 else (f == g)%:R).
Proof.
have F i j : 'chi_i != - 'chi[G]_ j.
  apply/negP=> Echi.
  have: '['chi_i] = 1 by rewrite cfdot_irr eqxx.
  rewrite  {1}(eqP Echi) cfdotNl cfdot_irr; case: (_ == _)=> /eqP.
    by rewrite eq_sym -subr_eq0 opprK -(natrD _ 1%N) -(eqN_eqC _ 0).
  by rewrite oppr0 -(eqN_eqC 0 1).
by case/dirrP=> [[]] [i1 ->] /dirrP [[]] [i2 ->];
   rewrite !(expr0, expr1, scaleN1r, scale1r, opprK, cfdotNr, cfdotNl);
   rewrite ?(eqr_opp, eqr_oppLR, cfdot_irr, (negPf (F _ _)));
   case: (boolP (i1 == _))=> [/eqP->|Di1i2];
   rewrite ?eqxx //; case: (_ =P _); rewrite ?oppr0 // => /chi_inj HH;
   case/eqP: Di1i2.
Qed.

Lemma dirr_norm1 phi : phi \in 'Z[irr G] -> '[phi] = 1 -> phi \in dirr G.
Proof.
move=> Zphi phiN1.
have: orthonormal phi by rewrite /orthonormal/= phiN1 eqxx.
case/vchar_orthonormalP=> [xi /predU1P[->|] // | I [b def_phi]].
have: phi \in (phi : seq _) := mem_head _ _.
rewrite (perm_eq_mem def_phi) => /mapP[i _ ->].
by rewrite dirr_sign dirr_chi.
Qed.

Lemma dirr_cfAut u phi : (cfAut u phi \in dirr G) = (phi \in dirr G).
Proof.
rewrite !dirrE vchar_cfAut; apply: andb_id2l => /cfdot_cfAut_vchar->.
exact: fmorph_eq1.
Qed.

Lemma signC_negb b : (-1) ^+ (~~ b) = - ((-1) ^+ b) :> algC.
Proof. by case: b => //; rewrite opprK. Qed.

Definition dIirr (B : {set gT}) := (bool * (Iirr B))%type.

Definition dirr1 (B : {set gT}) : dIirr B := (false, 0).

Definition ndirr (B : {set gT}) (i : dIirr B) : dIirr B := 
  (~~ i.1, i.2).

Lemma ndirr_diff (i : dIirr G) : ndirr i != i.
Proof. by case: i => [] [|] i. Qed.

Lemma ndirrK : involutive (@ndirr G).
Proof. by move=> [b i]; rewrite /ndirr /= negbK. Qed.

Lemma ndirr_inj : injective (@ndirr G).
Proof. exact: (inv_inj ndirrK). Qed.

Definition dchi (B : {set gT}) (i : dIirr B) : 'CF(B) := 
  (-1)^+ i.1 *: 'chi_i.2.

Lemma dchi1 : dchi (dirr1 G) = 1.
Proof. by rewrite /dchi scale1r chi0_1. Qed.

Lemma dirr_dchi i : dchi i \in dirr G.
Proof. by apply/dirrP; exists i.1; exists i.2. Qed.

Lemma dIrrP (phi : 'CF(G)) : 
  reflect (exists i , phi = dchi i) (phi \in dirr G).
Proof.
by apply: (iffP idP)=> [/dirrP [b [i ->]]| [i ->]]; 
      [exists (b, i) | exact: dirr_dchi].
Qed.

Lemma dchi_ndirrE (i : dIirr G) : dchi (ndirr i) = - dchi i.
Proof. by case: i => [b i]; rewrite /ndirr /dchi signC_negb scaleNr. Qed.

Lemma cfdot_dchi (i j : dIirr G) : 
  '[dchi i, dchi j] = (i == j)%:R - (i == ndirr j)%:R.
Proof.
case: i => bi i; case: j => bj j.
rewrite /dchi /ndirr /= cfdotZl cfdotZr cfdot_irr.
rewrite (isIntC_conj (isIntC_sign _)) mulrA -signr_addb.
rewrite {2 3}/eq_op /=; case: (_ == _); 
     rewrite ?(andbF, andbT, mulr1, mulr0, subrr) //.
by case: bi; case: bj=> //=; rewrite ?(subr0, sub0r).
Qed.

Lemma dchi_vchar i : dchi i \in 'Z[irr G].
Proof. by move:(dirr_dchi i); rewrite dirrE => /andP []. Qed.

Lemma cfnorm_dchi (i : dIirr G) : '[dchi i] = 1.
Proof. by rewrite cfdot_dchi eqxx eq_sym (negPf (ndirr_diff _)) subr0. Qed.

Lemma dchi_inj : injective (@dchi G).
Proof.
move=> i j Chi; move/eqP: (cfnorm_dchi i); rewrite {2}Chi cfdot_dchi.
by case: (i =P _)=> // _; rewrite sub0r; case: (i == _); 
  rewrite eq_sym -subr_eq0 opprK -(natrD _ 1%N) -(eqN_eqC _ 0).
Qed.

Definition dirr_dIirr (B : {set gT}) J (f : J -> 'CF(B)) j : dIirr B :=
  odflt (dirr1 B) [pick i | dchi i == f j].

Lemma dirr_dIirrPE J (f : J -> 'CF(G)) (P : pred J) :
    (forall j, P j -> f j \in dirr G) ->
  forall j, P j -> dchi (dirr_dIirr f j) = f j.
Proof.
rewrite /dirr_dIirr => dirrGf j Pj; case: pickP => [i /eqP //|].
by have /dIrrP[i-> /(_ i)/eqP] := dirrGf j Pj.
Qed.

Lemma dirr_dIirrE J (f : J -> 'CF(G)) :
  (forall j, f j \in dirr G) -> forall j, dchi (dirr_dIirr f j) = f j.
Proof. by move=> dirrGf j; exact: (@dirr_dIirrPE _ _ xpredT). Qed.

Definition dirr_constt (B : {set gT}) (phi: 'CF(B)) : {set (dIirr B)} :=  
  [set i | 0 < '[phi, dchi i]].

Lemma dirr_consttE (phi : 'CF(G)) (i : dIirr G) : 
  (i \in dirr_constt phi) = (0 < '[phi, dchi i]).
Proof. by rewrite inE. Qed.

Lemma isNatC_dirr (phi : 'CF(G)) i :
  phi \in 'Z[irr G] -> i \in dirr_constt phi -> isNatC('[phi, dchi i]).
Proof.
move=> PiZ; rewrite isNatC_posInt dirr_consttE => /ltCW ->.
case: i=> [b i]; rewrite andbT /dchi  cfdotZr (isIntC_conj (isIntC_sign _)).
by rewrite isIntC_mul ?isIntC_sign // cfdot_vchar_irr_Int.
Qed.
 
Lemma dirr_constt_oppr (i : dIirr G) (phi : 'CF(G)) : 
  (i \in dirr_constt (-phi)) = (ndirr i \in dirr_constt phi).
Proof. by rewrite !dirr_consttE dchi_ndirrE cfdotNl cfdotNr. Qed.

Lemma dirr_constt_oppI (phi: 'CF(G)) :
   dirr_constt phi :&: dirr_constt (-phi) = set0.
Proof.
apply/setP=> i; rewrite inE !dirr_consttE cfdotNl inE.
apply/idP=> /andP [L1 L2]; have := sposC_addl (ltCW L1) L2.
by rewrite subrr /ltC eqxx.
Qed.

Lemma dirr_constt_oppl (phi: 'CF(G)) i :
  i \in dirr_constt phi ->  (ndirr i) \notin dirr_constt phi.
Proof.
rewrite !dirr_consttE dchi_ndirrE cfdotNr sposC_opp.
by move/ltCW=> /leC_gtF ->.
Qed.

Definition to_dirr  (B : {set gT}) (phi : 'CF(B)) (i : Iirr B) : dIirr B := 
  ('[phi, 'chi_i] < 0, i).

Definition of_irr (B : {set gT}) (i : dIirr B) : Iirr B := i.2.

Lemma irr_constt_to_dirr (phi: 'CF(G)) i : phi \in 'Z[irr G] ->
  (i \in irr_constt phi) = (to_dirr phi i \in dirr_constt phi).
Proof.
move=> PiZ; rewrite irr_consttE dirr_consttE /dchi /to_dirr /=.
rewrite cfdotZr (isIntC_conj (isIntC_sign _)).
case: (boolP (_ == _)) => [/eqP-> | Di]; first by rewrite mulr0 /ltC eqxx.
case/realC_leP: (isIntC_Real (cfdot_vchar_irr_Int i PiZ)) => Dl0.
  have->: '[phi, 'chi_i] < 0 by rewrite /ltC eq_sym Di Dl0.
  by rewrite mulN1r sposC_opp /ltC eq_sym Di Dl0.
by rewrite (leC_gtF Dl0) mul1r /ltC Di Dl0.
Qed.

Lemma to_dirrK (phi: 'CF(G)) : cancel (to_dirr phi) (@of_irr G).
Proof. done. Qed.

Lemma of_irrK (phi: 'CF(G)) :
  {in dirr_constt phi, cancel (@of_irr G) (to_dirr phi)}.
Proof.
case=> b i; rewrite dirr_consttE /dchi /to_dirr /=.
rewrite cfdotZr (isIntC_conj (isIntC_sign _)).
by (case: b; rewrite ?(mulN1r, mul1r,sposC_opp))=> [-> //| /ltCW /leC_gtF ->].
Qed.

Lemma cfdot_todirrE (phi: 'CF(G)) i :  phi \in 'Z[irr G] ->
  '[phi, dchi (to_dirr phi i)] *: dchi (to_dirr phi i) = 
      '[phi, 'chi_i] *: 'chi_i.
Proof.
move=> PiZ.
rewrite /dchi /= cfdotZr (isIntC_conj (isIntC_sign _)) !scalerA.
by rewrite mulrAC -signr_addb addbb mul1r.
Qed.

Lemma cfun_sum_dconstt (phi : 'CF(G)) :
  phi \in 'Z[irr G] ->
  phi = \sum_(i \in dirr_constt phi) '[phi, dchi i] *: dchi i.
Proof.
(* GG -- rewrite pattern fails in trunk
  move=> PiZ; rewrite [X in X = _]cfun_sum_constt. *)
move=> PiZ; rewrite {1}[phi]cfun_sum_constt.
rewrite (reindex (to_dirr phi))=> [/= |]; last first.
  by exists (@of_irr _)=> //; exact: of_irrK .
by apply: eq_big=> i; rewrite ?irr_constt_to_dirr // cfdot_todirrE.
Qed.

Lemma cnorm_dconstt (phi : 'CF(G)) :
  phi \in 'Z[irr G] ->
  '[phi] = \sum_(i \in dirr_constt phi) '[phi, dchi i] ^+ 2.
Proof.
move=> PiZ; rewrite {1 2}(cfun_sum_dconstt PiZ).
rewrite cfdot_suml; apply: eq_bigr=> i IiD.
rewrite cfdot_sumr (bigD1 i) //= big1 ?addr0 => [|j /andP [JiD IdJ]].
  rewrite cfdotZr cfdotZl cfdot_dchi.
  rewrite eqxx eq_sym (negPf (ndirr_diff i)) subr0 mulr1.
  by rewrite isNatC_conj // isNatC_dirr.
rewrite cfdotZr cfdotZl cfdot_dchi eq_sym (negPf IdJ).
case: (boolP (_ == _))=> [IeN|]; last by rewrite subrr !mulr0.
by case/negP: (dirr_constt_oppl JiD); rewrite -(eqP IeN).
Qed.

Lemma dirr_small_norm (phi : 'CF(G)) n :
  phi \in 'Z[irr G] -> '[phi] = n%:R -> (n < 4)%N ->
  [/\ #|dirr_constt phi| = n, dirr_constt phi :&: dirr_constt (-phi) = set0 & 
      phi = \sum_(i \in dirr_constt phi) dchi i].
Proof.
move=> PiZ Pln; rewrite ltnNge leq_leC => Nl4.
suff Fd: forall i : dIirr G, i \in dirr_constt phi -> '[phi, dchi i] = 1.
  split.
  - apply/eqP; rewrite eqN_eqC; apply/eqP.
    rewrite -sumr_const -Pln (cnorm_dconstt PiZ).
    by apply: eq_bigr=> i Hi; rewrite Fd // expr1n.
  - set A := (_ :&: _); case: (set_0Vmem A)=> // [[u]]; rewrite !inE cfdotNl.
    by rewrite sposC_opp; case/andP; move/ltCW => /leC_gtF->.
  rewrite {1}(cfun_sum_dconstt PiZ).
  by apply: eq_bigr=> i Hi; rewrite Fd // scale1r.
move=> i IiD; move: Pln; rewrite (cnorm_dconstt PiZ).
rewrite (bigD1 i) //=; move: (isNatC_dirr PiZ IiD) (IiD).
rewrite dirr_consttE => /isNatCP=> [[[|[|m]]]] -> //.
  by rewrite /ltC eqxx.
move=> _ HH; case/negP: Nl4; rewrite -HH -natrX /=.
have->: (m.+2 ^ 2 = 4 + ((m.+2) * m + 2 * m))%N by ring.
rewrite natrD -addrA addrC -leC_sub addrK posC_add ?posC_nat //.
apply: posC_sum => j /andP [JiD _].
by case/isNatCP: (isNatC_dirr PiZ JiD)=> k ->; apply: posC_exp (posC_nat _).
Qed.

Lemma cfdot_sum_dchi (phi1 phi2 : 'CF(G)) :
  '[\sum_(i \in dirr_constt phi1) dchi i,
    \sum_(i \in dirr_constt phi2) dchi i] = 
  #|dirr_constt phi1 :&: dirr_constt phi2|%:R -
    #|dirr_constt phi1 :&: dirr_constt (-phi2)|%:R.
Proof.
rewrite (bigID [pred i | i \in dirr_constt phi1 :&: dirr_constt phi2]) /=.
rewrite cfdotDl; congr (_ + _).
  rewrite cfdot_suml -sumr_const; apply: eq_big => [i|i /andP [_ ]].
    by rewrite !inE andbA andbb.
  rewrite inE => /andP [IiD1 IiD2]; rewrite cfdot_sumr (bigD1 i) //=.
  rewrite cfnorm_dchi big1 ?addr0 // => j /andP [JiD2 JdI].
  rewrite cfdot_dchi eq_sym (negPf JdI) sub0r.
  case: (boolP (_ == _))=> HH; last by rewrite mulr0n oppr0.
  by case/negP: (dirr_constt_oppl JiD2); rewrite -(eqP HH).
rewrite (bigID [pred i | i \in dirr_constt phi1 :&: dirr_constt (-phi2)]) /=.
rewrite cfdotDl !cfdot_suml [X in _ + X = _]big1 ?addr0.
  rewrite -sumr_const -sumrN; apply: eq_big => [i|i /andP []].
    rewrite !inE; case: (0 < _)=> //=; rewrite cfdotNl sposC_opp.
    by case: (boolP (_ < 0)); [move/ltCW=> /leC_gtF-> | rewrite andbF].
  case/andP=> _; rewrite inE negb_and => IoD1D2.
  rewrite inE => /andP [IiD1 IiND2]; rewrite cfdot_sumr.
  rewrite (bigD1 (ndirr i)) /=; last by rewrite -dirr_constt_oppr.
  rewrite cfdot_dchi ndirrK eqxx eq_sym (negPf (ndirr_diff _)) sub0r.
  rewrite big1 ?addr0 // => j /andP [IiD2 JdNi].
  rewrite cfdot_dchi; case: (boolP (_ == _))=> E1.
    by case/orP: IoD1D2 => /negP [] //; rewrite (eqP E1).
  case: (boolP (_ == _))=> E2; last by rewrite subrr.
  by case/negP: JdNi; rewrite (eqP E2) ndirrK.
move=> i /andP [/andP [IiD1]]; rewrite inE IiD1 /= => IniD2.
rewrite inE IiD1 /= => IniND2; rewrite cfdot_sumr big1 // => j JiD2.
rewrite cfdot_dchi; case: (boolP (_ == _))=> E1.
  by case/negP: IniD2; rewrite (eqP E1).
case: (boolP (_ == _))=> E2; last by rewrite subrr.
by case/negP: IniND2; rewrite (eqP E2) dirr_constt_oppr ndirrK.
Qed.

Lemma cfdot_dirr_eq1 :
  {in dirr G &, forall phi psi, ('[phi, psi] == 1) = (phi == psi)}.
Proof.
move=> _ _ /dirrP[b1 [i1 ->]] /dirrP[b2 [i2 ->]].
rewrite eq_signed_irr cfdotZl cfdotZr rmorph_sign cfdot_irr mulrA -signr_addb.
rewrite signrE mulrBl (can2_eq (subrK _) (addrK _)) mul1r -natrM.
rewrite -(natrD _ 1) -eqN_eqC -negb_add.
by case: (i1 == _) (_ (+) _) => [] [].
Qed.

Lemma cfdot_add_dirr_eq1 :
  {in dirr G & &, forall phi1 phi2 psi,
    '[phi1 + phi2, psi] = 1 -> psi = phi1 \/ psi = phi2}.
Proof.
move=> _ _ _ /dirrP[b1 [i1 ->]] /dirrP[b2 [i2 ->]] /dirrP[c [j ->]] /eqP.
rewrite cfdotDl !cfdotZl !cfdotZr !rmorph_sign !cfdot_irr !mulrA -!signr_addb.
rewrite 2!{1}signrE !mulrBl !mul1r -!natrM addrCA -subr_eq0 -!addrA.
rewrite -!opprD addrA subr_eq0 -mulrSr -!natrD -eqN_eqC => eq_phi_psi.
apply/pred2P; rewrite /= !eq_signed_irr -!negb_add !(eq_sym j) !(addbC c).
by case: (i1 == j) eq_phi_psi; case: (i2 == j); do 2!case: (_ (+) c).
Qed.

End Norm1vchar.
