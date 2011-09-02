(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius.
Require Import matrix mxalgebra mxrepresentation vector.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.

(******************************************************************************)
(* This file covers Peterfalvi, Section 5: Coherence.                         *)
(* Defined here:                                                              *)
(*    coherent S A tau <-> (S, A, tau) is coherent, i.e., there is a linear   *)
(*                         isometry from 'Z[S] to 'Z[irr G] that coincides    *)
(*                         with tau on 'Z[S, A] (where S : seq 'CF(L)).       *)
(* subcoherent S tau R <-> S : seq 'cfun(L) is non empty, pairwise orthogonal *)
(*                         and closed under complex conjugation, tau is an    *)
(*                         isometry from 'Z[S, L^#] to virtual characters in  *)
(*                         G that maps the difference chi - chi^*, for each   *)
(*                         chi \in S, sum of an orthonormal family R chi of   *)
(*                         virtual characters of G; in addition R chi and     *)
(*                         R phi are orthogonal unless phi \in chi :: chi^*.  *)
(* We provide a set of definitions that cover the various \cal S notations    *)
(* introduces in Peterfalvi sections 5, 6, 7, and 9 to 14.                    *)
(*         Iirr_ker K A == the set of all i : Iirr K such that the kernel of  *)
(*                         'chi_i contains A.                                 *)
(*      Iirr_kerD K B A == the set of all i : Iirr K such that the kernel of  *)
(*                         'chi_i contains A but not B.                       *)
(*        seqInd L calX == the duplicate-free sequence of characters of L     *)
(*                         induced from K by the 'chi_i for i in calX.        *)
(*          seqIndT K L == the duplicate-free sequence of all characters of L *)
(*                         induced by irreducible characters of K.            *)
(*      seqIndD K L H M == the duplicate-free sequence of characters of L     *)
(*                         induced by irreducible characters of K that have M *)
(*                         in their kernel, but not H.                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* Results about the set of induced irreducible characters *)
Section InducedIrrs.

Variables (gT : finGroupType) (K L : {group gT}).
Implicit Types (A B : {set gT}) (H M : {group gT}).
Implicit Type u : {rmorphism algC -> algC}.

Section KerIirr.

Definition Iirr_ker A := [set i | A \subset cfker 'chi[K]_i].

Lemma Iirr_kerS A B : B \subset A -> Iirr_ker A \subset Iirr_ker B.
Proof. by move/subset_trans=> sBA; apply/subsetP=> i; rewrite !inE => /sBA. Qed.

Lemma sum_Iirr_ker_square H :
  H <| K -> \sum_(i \in Iirr_ker H) 'chi_i 1%g ^+ 2 = #|K : H|%:R.
Proof.
move=> nsHK; rewrite -card_quotient ?normal_norm // -irr_sum_square.
rewrite (eq_bigl _ _ (in_set _)) (reindex _ (mod_Iirr_bij nsHK)) /=.
by apply: eq_big => [i | i _]; rewrite mod_IirrE ?cfker_Mod ?cfMod1.
Qed.

Definition Iirr_kerD B A := Iirr_ker A :\: Iirr_ker B.

Lemma sum_Iirr_kerD_square H M :
    H <| K -> M <| K -> M \subset H ->
  \sum_(i \in Iirr_kerD H M) 'chi_i 1%g ^+ 2 = #|K : H|%:R * (#|H : M|%:R - 1).
Proof.
move=> nsHK nsMK sMH; have [sHK _] := andP nsHK.
rewrite mulr_subr mulr1 -natr_mul LaGrange_index // -!sum_Iirr_ker_square //.
apply/esym/(canLR (addrK _)); rewrite /= addrC (big_setID (Iirr_ker H)).
by rewrite (setIidPr _) ?Iirr_kerS //.
Qed.

Lemma Iirr_ker_Aut u A i : (aut_Iirr u i \in Iirr_ker A) = (i \in Iirr_ker A).
Proof. by rewrite !inE aut_IirrE cfker_Aut. Qed.

Lemma Iirr_ker_conjg A i x :
  x \in 'N(A) -> (conjg_Iirr i x \in Iirr_ker A) = (i \in Iirr_ker A).
Proof.
move=> nAx; rewrite !inE conjg_IirrE.
have [nKx | /cfConjg_out-> //] := boolP (x \in 'N(K)).
by rewrite cfker_conjg // -{1}(normP nAx) conjSg.
Qed.

Lemma Iirr_kerDS A1 A2 B1 B2 :
  A2 \subset A1 -> B1 \subset B2 -> Iirr_kerD B1 A1 \subset Iirr_kerD B2 A2.
Proof. by move=> sA12 sB21; rewrite setDSS ?Iirr_kerS. Qed.

Lemma Iirr_kerDY B A : Iirr_kerD (A <*> B) A = Iirr_kerD B A. 
Proof. by apply/setP=> i; rewrite !inE join_subG; apply: andb_id2r => ->. Qed.

Lemma mem_Iirr_ker1 i : (i \in Iirr_kerD K 1%g) = (i != 0).
Proof. by rewrite !inE sub1G andbT subGcfker. Qed.

End KerIirr.

Hypothesis nsKL : K <| L.
Let sKL := normal_sub nsKL.
Let nKL := normal_norm nsKL.
Let e := #|L : K|%:R : algC.
Let nze : e != 0 := neq0GiC _ _.

Section SeqInd.

Variable calX : {set (Iirr K)}.

(* The set of characters induced from the irreducibles in calX. *)
Definition seqInd := undup [image 'Ind[L] 'chi_i | i <- calX].
Local Notation S := seqInd.

Lemma seqInd_uniq : uniq S. Proof. exact: undup_uniq. Qed.

Lemma seqIndP phi :
  reflect (exists2 i, i \in calX & phi = 'Ind[L] 'chi_i) (phi \in S).
Proof. by rewrite mem_undup; exact: imageP. Qed.

Lemma seqInd_on : {subset S <= 'CF(L, K)}.
Proof. by move=> _ /seqIndP[i _ ->]; exact: cfInd_normal. Qed.

Lemma seqInd_char : all is_char S.
Proof. by apply/allP=> _ /seqIndP[i _ ->]; rewrite cfInd_char ?irr_char. Qed.

Lemma seqInd1_Nat phi : phi \in S -> isNatC (phi 1%g).
Proof. by move/(allP seqInd_char)/char1_Nat. Qed.

Lemma seqInd1_Int phi : phi \in S -> isIntC (phi 1%g).
Proof. by rewrite isIntCE; move/seqInd1_Nat->. Qed.

Lemma seqInd_neq0 psi : psi \in S -> psi != 0.
Proof. by move=> /seqIndP[i _ ->]; exact: Ind_irr_neq0. Qed.

Lemma seqInd1_neq0 psi : psi \in S -> psi 1%g != 0.
Proof. by move=> Spsi; rewrite char1_eq0 ?(allP seqInd_char) ?seqInd_neq0. Qed.

Lemma cfnorm_seqInd_neq0 psi : psi \in S -> '[psi] != 0.
Proof. by move/seqInd_neq0; rewrite cfnorm_eq0. Qed.

Lemma seqInd_ortho : {in S &, forall phi psi, phi != psi -> '[phi, psi] = 0}.
Proof.
move=> _ _ /seqIndP[i _ ->] /seqIndP[j _ ->].
by case: ifP (cfclass_irr_induced i j nsKL) => // _ -> /eqP.
Qed.

Lemma seqInd_orthogonal : pairwise_orthogonal S.
Proof.
apply/pairwise_orthogonalP; split; last exact: seqInd_ortho.
by rewrite /= undup_uniq andbT; move/memPn: seqInd_neq0.
Qed.

Lemma seqInd_free : free S.
Proof. exact: (orthogonal_free seqInd_orthogonal). Qed.

Lemma seqInd_vcharW : {subset S <= 'Z[S]}.
Proof. by move=> phi Sphi; rewrite mem_vchar ?seqInd_free. Qed.

Lemma seqInd_vchar : {subset S <= 'Z[S, K]}.
Proof. by move=> phi Sphi; rewrite vchar_split seqInd_vcharW ?seqInd_on. Qed.

Lemma seqInd_virrW : {subset S <= 'Z[irr L]}.
Proof. by move=> phi Sphi; rewrite char_vchar ?(allP seqInd_char). Qed.

Lemma seqInd_virr : {subset S <= 'Z[irr L, K]}.
Proof. by move=> phi Sphi; rewrite vchar_split seqInd_virrW ?seqInd_on. Qed.

Lemma dvd_index_seqInd1 phi : phi \in S -> isNatC (phi 1%g / e).
Proof.
by case/seqIndP=> i _ ->; rewrite cfInd1 // mulrC mulKf ?isNatC_irr1.
Qed.

Lemma sub_seqInd_vchar phi psi :
  phi \in S -> psi \in S -> psi 1%g *: phi - phi 1%g *: psi \in 'Z[S, K^#].
Proof.
move=> Sphi Spsi; rewrite vcharD1 !cfunE mulrC subrr eqxx.
by rewrite sub_vchar ?scale_vchar ?seqInd1_Int ?seqInd_vchar.
Qed.

Lemma sub_seqInd_on phi psi :
  phi \in S -> psi \in S -> psi 1%g *: phi - phi 1%g *: psi \in 'CF(L, K^#).
Proof. by move=> Sphi Spsi; exact: vchar_on (sub_seqInd_vchar Sphi Spsi). Qed.

Section Beta.

Variable xi : 'CF(L).
Hypotheses (Sxi : xi \in S) (xi1 : xi 1%g = e).

Lemma cfInd1_sub_lin_vchar : 'Ind[L, K] 1 - xi \in 'Z[irr L, K^#].
Proof.
rewrite vcharD1 !cfunE xi1 cfInd1 // cfun1E group1 mulr1 subrr eqxx andbT.
rewrite sub_vchar ?(seqInd_virr Sxi) // vchar_split cfInd_normal ?char_vchar //.
by rewrite cfInd_char ?cfun1_char.
Qed.

Lemma cfInd1_sub_lin_on : 'Ind[L, K] 1 - xi \in 'CF(L, K^#).
Proof. exact: vchar_on cfInd1_sub_lin_vchar. Qed.

Lemma seqInd_sub_lin_vchar :
  {in S, forall phi : 'CF(L), phi - (phi 1%g / e) *: xi \in 'Z[S, K^#]}.
Proof.
move=> phi Sphi; rewrite /= vcharD1 !cfunE xi1 divfK // subrr eqxx.
by rewrite sub_vchar ?scale_vchar ?seqInd_vchar // isIntCE dvd_index_seqInd1.
Qed.

Lemma seqInd_sub_lin_on :
  {in S, forall phi : 'CF(L), phi - (phi 1%g / e) *: xi \in 'CF(L, K^#)}.
Proof. by move=> phi /seqInd_sub_lin_vchar/vchar_on. Qed.

End Beta.

End SeqInd.

Implicit Arguments seqIndP [calX phi].

Lemma seqIndS (calX calY : {set Iirr K}) :
 calX \subset calY -> {subset seqInd calX <= seqInd calY}.
Proof.
by move=> sXY _ /seqIndP[i /(subsetP sXY)Yi ->]; apply/seqIndP; exists i.
Qed.

Definition seqIndT := seqInd setT.

Lemma seqInd_subT calX : {subset seqInd calX <= seqIndT}.
Proof. exact: seqIndS (subsetT calX). Qed.

Lemma seqIndT_Ind1 : 'Ind[L, K] 1 \in seqIndT.
Proof. by apply/seqIndP; exists 0; rewrite ?chi0_1 ?inE. Qed.

Implicit Arguments seqIndP [calX phi].

Definition seqIndD H M := seqInd (Iirr_kerD H M).

Lemma seqIndDY H M : seqIndD (M <*> H) M = seqIndD H M.
Proof. by rewrite /seqIndD Iirr_kerDY. Qed.

Lemma mem_seqInd H M i :
  H <| L -> M <| L -> ('Ind 'chi_i \in seqIndD H M) = (i \in Iirr_kerD H M).
Proof.
move=> nsHL nsML; apply/seqIndP/idP=> [[j Xj] | Xi]; last by exists i.
case/cfclass_Ind_irrP/cfclassP=> // y Ly; rewrite -conjg_IirrE => /chi_inj->.
by rewrite inE !Iirr_ker_conjg -?in_setD ?(subsetP _ y Ly) ?normal_norm.
Qed.

Lemma seqIndC1P phi :
  reflect (exists2 i, i != 0 & phi = 'Ind 'chi[K]_i) (phi \in seqIndD K 1).
Proof.
by apply: (iffP seqIndP) => [] [i nzi ->];
  exists i; rewrite // mem_Iirr_ker1 in nzi *.
Qed.

Lemma seqIndC1_filter : seqIndD K 1 = filter (predC1 ('Ind[L, K] 1)) seqIndT.
Proof.
rewrite filter_undup filter_map (eq_enum (in_set _)) enumT.
congr (undup (map _ _)); apply: eq_filter => i /=.
by rewrite mem_Iirr_ker1 cfInd_irr_eq1.
Qed.

Lemma seqIndC1_rem : seqIndD K 1 = rem ('Ind[L, K] 1) seqIndT.
Proof. by rewrite rem_filter ?seqIndC1_filter ?undup_uniq. Qed.

Section SeqIndD.

Variables H M : {group gT}.

Local Notation S := (seqIndD H M).

Lemma cfAut_seqInd u : cfAut_closed u S.
Proof.
move=> _ /seqIndP[i /setDP[kMi not_kHi] ->]; rewrite cfAutInd -aut_IirrE.
by apply/seqIndP; exists (aut_Iirr u i); rewrite // inE !Iirr_ker_Aut not_kHi.
Qed.

Lemma seqInd_sub_Aut_vchar u :
  {in S, forall phi, phi - cfAut u phi \in 'Z[S, K^#]}.
Proof.
move=> phi Sphi /=; rewrite sub_Aut_vchar ?seqInd_vchar ?cfAut_seqInd //.
exact: seqInd_virrW.
Qed.

Hypothesis sHK : H \subset K.

Lemma seqInd_sub : {subset S <= seqIndD K 1}.
Proof. by apply: seqIndS; exact: Iirr_kerDS (sub1G M) sHK. Qed.

Lemma seqInd_ortho_Ind1 : {in S, forall phi, '[phi, 'Ind[L, K] 1] = 0}.
Proof.
move=> _ /seqInd_sub/seqIndC1P[i nzi ->].
by rewrite -chi0_1 not_cfclass_Ind_ortho // chi0_1 cfclass1 // inE irr_eq1.
Qed.

Lemma seqInd_ortho_cfuni : {in S, forall phi, '[phi, '1_K] = 0}.
Proof.
move=> phi /seqInd_ortho_Ind1/eqP; apply: contraTeq => not_o_phi_1K.
by rewrite cfInd_cfun1 // cfdotZr rmorph_nat mulf_neq0.
Qed.

Lemma seqInd_ortho_1 : {in S, forall phi, '[phi, 1] = 0}.
Proof.
move=> _ /seqInd_sub/seqIndC1P[i nzi ->].
by rewrite -cfdot_Res_r cfRes_cfun1 // -chi0_1 cfdot_irr (negbTE nzi).
Qed.

Lemma seqInd_conjC_ortho :
  odd #|L| -> {in S, forall phi, '[phi, (phi^*)%CF] = 0}.
Proof.
move=> oddL _  /seqInd_sub/seqIndC1P[i nzi ->]; exact: odd_induced_orthogonal.
Qed.

Lemma seqInd_notReal : odd #|L| -> ~~ has cfReal S.
Proof.
move=> oddL; apply/hasP=> [[phi Sphi /(_ =P phi) Rphi]].
by case/eqP: (cfnorm_seqInd_neq0 Sphi); rewrite -{2}Rphi seqInd_conjC_ortho.
Qed.

Lemma seqInd_conjC_ortho2 r :
  odd #|L| -> 'chi_r \in S -> orthonormal ('chi_r :: ('chi_r)^*)%CF.
Proof.
move=> oddL Schi; apply/orthonormal2P.
by rewrite -{-1}conjC_IirrE !cfnorm_irr seqInd_conjC_ortho.
Qed.

Lemma sum_seqIndD_square :
    H <| L -> M <| L -> M \subset H ->
  \sum_(phi <- S) phi 1%g ^+ 2 / '[phi] = #|L : H|%:R * (#|H : M|%:R - 1).
Proof.
move=> nsHL nsML sMH; rewrite -(LaGrange_index sKL sHK) natr_mul -/e -mulrA.
rewrite -sum_Iirr_kerD_square ?(normalS _ sKL) ?(subset_trans sMH) //.
pose h i := @Ordinal (size S).+1 _ (index_size ('Ind 'chi[K]_i) S).
rewrite (partition_big h (ltn^~ (size S))) => /= [|i Xi]; last first.
  by rewrite index_mem mem_seqInd.
rewrite big_distrr big_ord_narrow //= big_index_uniq ?seqInd_uniq //=.
apply: eq_big_seq => phi Sphi; rewrite /eq_op insubT ?index_mem //= => _.
have /seqIndP[i kHMi def_phi] := Sphi.
have/cfunP/(_ 1%g) := induced_sum_rcosets1 i nsKL.
rewrite !cfunE sum_cfunE -def_phi cfResE // mulrAC => ->; congr (_ * _).
rewrite -cfclass_sum //=; apply/esym/eq_big => j; last by rewrite !cfunE.
rewrite (sameP (cfclass_Ind_irrP _ _ nsKL) eqP) -def_phi -mem_seqInd //.
by apply/andP/eqP=> [[/(nth_index 0){2}<- /eqP->] | -> //]; exact: nth_index.
Qed.

End SeqIndD.

Lemma sum_seqIndC1_square :
  \sum_(phi <- seqIndD K 1) phi 1%g ^+ 2 / '[phi] = e * (#|K|%:R - 1).
Proof. by rewrite sum_seqIndD_square ?normal1 ?sub1G // indexg1. Qed.

End InducedIrrs.

Implicit Arguments seqIndP [gT K L calX phi].
Implicit Arguments seqIndC1P [gT K L phi].

Section Five.

Variable gT : finGroupType.

(* This is Peterfalvi, Definition (5.1). *)
(* We depart from the text in Section 5 by dropping non-triviality condition, *)
(* which is not used consistently in the rest of the proof; in particular, it *)
(* is incompatible with the use of "not coherent" in (6.2), and it is only    *)
(* really used in (7.8), where a weaker condition (size S > 1) would suffice. *)
Definition coherent (L G : {set gT}) S A tau :=
  exists2 tau1 : {linear 'CF(L) -> 'CF(G)},
     {in 'Z[S], isometry tau1, to 'Z[irr G]}
   & {in 'Z[S, A], tau1 =1 tau}.

(* This is Peterfalvi, Hypothesis (5.2). *)
(* The Z-linearity constraint on tau will be expressed by an additive or      *)
(* linear structure on tau.                                                   *)
Definition subcoherent L G S tau R :=
  [/\ (*a*) [/\ all is_char S, ~~ has cfReal S & conjC_closed S],
      (*b*) {in 'Z[S, L^#], isometry tau, to 'Z[@irr gT G, G^#]},
      (*c*) pairwise_orthogonal S,
      (*d*) {in S, forall xi : 'CF(L : {set gT}),
              [/\ {subset R xi <= 'Z[irr G]}, orthonormal (R xi)
                & tau (xi - xi^*)%CF = \sum_(alpha <- R xi) alpha]}
    & (*e*) {in S &, forall xi phi : 'CF(L),
              orthogonal phi (xi :: xi^*%CF) -> orthogonal (R phi) (R xi)}].

Section SubsetCoherent.

Variables (L G : {group gT}) (tau : 'CF(L) -> 'CF(G)).

Lemma subgen_coherent A S1 S2 :
  {subset S2 <= 'Z[S1]} -> coherent S1 A tau -> coherent S2 A tau.
Proof.
move/vchar_trans=> sS21 [tau1 [Itau1 Ztau1] def_tau].
exists tau1; last exact: sub_in1 def_tau.
by split; [exact: sub_in2 Itau1 | exact: sub_in1 Ztau1].
Qed.

Lemma subset_coherent A S1 S2 :
  {subset S2 <= S1} -> free S1 -> coherent S1 A tau -> coherent S2 A tau.
Proof.
by move=> sS21 freeS1; apply: subgen_coherent => phi /sS21/mem_vchar->.
Qed.

Lemma perm_eq_coherent A S1 S2 :
  perm_eq S1 S2 -> free S1 -> coherent S1 A tau -> coherent S2 A tau.
Proof.
by move=> eqS12; apply: subset_coherent => phi; rewrite (perm_eq_mem eqS12).
Qed.

End SubsetCoherent.

(* This is Peterfalvi (5.2)(a). *)
Lemma irr_subcoherent (L G : {group gT}) S tau :
    [/\ uniq S, {subset S <= irr L}, ~~ has cfReal S & conjC_closed S] ->
    {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]} ->
  {R | subcoherent S tau R}.
Proof.
move=> [U_S irrS nrS ccS] [isoL Ztau].
have N_S: all is_char S by  apply/allP=> _ /irrS/irrP[i ->]; exact: irr_char.
have vcS: {subset S <= 'Z[irr L]} by move=> chi /(allP N_S)/char_vchar.
have orthS: pairwise_orthogonal S.
  apply/orthonormal_orthogonal/orthonormalP.
  split=> //= _ _ /irrS/irrP[i ->] /irrS/irrP[j ->].
  by rewrite (inj_eq (@chi_inj _ L)) cfdot_irr.
have freeS := orthogonal_free orthS.
pose beta chi := tau (chi - chi^*)%CF; pose eqBP := _ =P beta _.
have Zbeta: {in S, forall chi, chi - (chi^*)%CF \in 'Z[S, L^#]}.
  move=> chi Schi.
  have [/irrP[i def_chi] Schi'] := (irrS _ Schi, ccS _ Schi).
  rewrite vchar_split cfunD1E sub_vchar ?mem_vchar ?subT //= def_chi.
  by rewrite !cfunE isNatC_conj ?isNatC_irr1 ?subrr.
pose sum_beta chi R := \sum_(alpha <- R) alpha == beta chi. 
pose Zortho R := all (mem 'Z[irr G]) R && orthonormal R.
have R chi: {R : 2.-tuple 'CF(G) | (chi \in S) ==> sum_beta chi R && Zortho R}.
  apply: sigW; case Schi: (chi \in S) => /=; last by exists [tuple 0; 0].
  move/(_ _ Schi) in Zbeta; have /irrP[i def_chi] := irrS _ Schi.
  have: '[beta chi] = 2%:R.
    have Schi' := ccS _ Schi.
    rewrite isoL // cfnormD cfnormN cfdotNr def_chi -conjC_IirrE !cfdot_irr.
    rewrite !eqxx -(inj_eq (@chi_inj _ L)) conjC_IirrE -def_chi eq_sym.
    by rewrite -[_ == _]negbK (hasPn nrS) // oppr0 rmorph0 !addr0 -natr_add.
  case/vchar_small_norm; rewrite ?(vcharW (Ztau _ _)) // => R [oR ZR sumR].
  by exists R; apply/and3P; split; [exact/eqP | exact/allP | ].
exists (fun xi => val (val (R xi))); split=> // [chi Schi | chi phi Schi Sphi].
  by case: (R chi) => Rc /=; rewrite Schi => /and3P[/eqBP-> /allP].
case/andP => /and3P[/= /eqP opx /eqP opx' _] _.
have{opx opx'} obpx: '[beta phi, beta chi] = 0.
  rewrite isoL ?Zbeta // cfdot_subl !cfdot_subr -{3}[chi]cfConjCK.
  by rewrite !cfdot_conjC opx opx' rmorph0 !subr0.
case: (R phi) => [[[|a [|b []]] //= _]].
rewrite Sphi => /and3P[/eqBP sum_ab Zab o_ab].
case: (R chi) => [[[|c [|d []]] //= _]].
rewrite Schi => /and3P[/eqBP sum_cd Zcd o_cd].
suffices: orthonormal [:: a; - b; c; d].
  rewrite (orthonormal_cat [:: a; _]) => /and3P[_ _].
  by rewrite /orthogonal /= !cfdotNl !oppr_eq0.
apply: vchar_pairs_orthonormal 1 (-1) _ _ _ _.
- by split; apply/allP; rewrite //= opp_vchar.
- by rewrite o_cd andbT /orthonormal/= cfnormN /orthogonal /= cfdotNr !oppr_eq0.
- by rewrite oppr_eq0 oner_eq0 /isRealC rmorphN rmorph1 !eqxx.
rewrite !(big_seq1, big_cons) in sum_ab sum_cd.
rewrite scale1r scaleN1r !opprK sum_ab sum_cd obpx eqxx /=.
by rewrite !(cfun_on0 (vchar_on (Ztau _ _))) ?Zbeta ?inE ?eqxx.
Qed.

Section SubCoherentProperties.

Variables (L G : {group gT}) (S : seq 'CF(L)) (R : 'CF(L) -> seq 'CF(G)).
Variable tau : {linear 'CF(L) -> 'CF(G)}.
Hypothesis cohS : subcoherent S tau R.

Lemma nil_coherent A : coherent [::] A tau.
Proof.
exists [linear of 'Ind[G]] => [|u]; last first.
  by rewrite inE /= span_nil memv0 => /andP[/eqP->]; rewrite !linear0.
split=> [u v | u]; rewrite inE /= span_nil memv0 => /andP[/eqP-> _].
  by rewrite inE /= span_nil memv0 => /andP[/eqP->]; rewrite !linear0 !cfdot0r.
by rewrite linear0 cfun0_vchar.
Qed.

Lemma subset_subcoherent S1 :
  [/\ uniq S1, {subset S1 <= S} & conjC_closed S1] -> subcoherent S1 tau R.
Proof.
case=> uS1 sS1 ccS1; have [[N_S nrS _] Itau oS defR oR] := cohS.
split; last 1 [exact: sub_in1 defR | exact: sub_in2 oR].
- split=> //; first by apply/allP=> xi /sS1/(allP N_S).
  by apply/hasPn; exact: sub_in1 (hasPn nrS).
- apply: sub_iso_to Itau => //; apply: vchar_subset => //.
  exact: orthogonal_free.
exact: sub_pairwise_orthogonal oS.
Qed.

Lemma subcoherent_split chi beta :
    chi \in S -> beta \in 'Z[irr G] ->
  exists X, exists Y,
    [/\  beta = X - Y, X \in 'Z[R chi] & orthogonal Y (R chi)].
Proof.
move=> Schi Zbeta; pose X := \sum_(a <- R chi) '[beta, a] *: a.
have [_ _ _ /(_ _ Schi)[ZR ortnR _] _] := cohS.
exists X, (X - beta); split; first by rewrite oppr_add addNKr opprK.
  rewrite /X big_seq sum_vchar //= => a Ra.
  by rewrite scale_vchar ?mem_vchar ?orthonormal_free ?cfdot_vchar_Int // ZR.
apply/orthogonalP=> _ a /predU1P[->|//] Ra.
by rewrite cfdot_subl cfproj_sum_orthonormal ?subrr.
Qed.

(* This is Peterfalvi (5.4). *)
Lemma subcoherent_norm chi psi (tau1 : {linear 'CF(L) -> 'CF(G)}) X Y :
    [/\ chi \in S, psi \in 'Z[irr L] & orthogonal (chi :: chi^*)%CF psi] ->
    let S0 := chi - psi :: chi - chi^*%CF in
    {in 'Z[S0], isometry tau1, to 'Z[irr G]} ->
    tau1 (chi - chi^*)%CF = tau (chi - chi^*)%CF ->
    [/\ tau1 (chi - psi) = X - Y, X \in 'Z[R chi] & orthogonal Y (R chi)] ->
 [/\ (*a*) '[chi] <= '[X]
   & (*b*) '[psi] <= '[Y] ->
           [/\ '[X] = '[chi], '[Y] = '[psi]
             & exists2 E, subseq E (R chi) & X = \sum_(a <- E) a]].
Proof.
case=> Schi Zpsi /and3P[/andP[/eqP ocp _] /andP[/eqP oc'p _] _] S0 [iso_t1 Zt1].
move=> t1cc' [defXY ZX oYR].
have [[ZS nrS ccS] [tS Zt] oS /(_ _ Schi)[ZR onR tcc'] _] := cohS.
have [_ oSS] := pairwise_orthogonalP oS.
have [ne_cc' Sc'] := (hasPn nrS _ Schi, ccS _ Schi).
have nzc: chi != 0 by apply: contraNneq ne_cc' => ->; rewrite /cfReal raddf0.
have freeS0: free S0.
  apply/freeP=> b /=; rewrite big_ord_recl big_ord1 /= => b0.
  have b10: b (lift 0 0) = 0.
    apply/eqP; have /eqP := congr1 (cfdot chi^*) b0.
    rewrite /= cfdot0r cfdotDr !cfdotZr !cfdot_subr oSS // oc'p.
    rewrite subrr mulr0 sub0r add0r mulf_eq0 conjC_eq0 oppr_eq0 cfnorm_eq0.
    by rewrite (inv_eq (@cfConjCK _ L)) raddf0 (negbTE nzc) orbF.
  move=> i; apply/eqP; move: i isT; apply/forall_inP; rewrite -big_andE.
  rewrite big_ord_recl big_ord1 b10 eqxx andbT.
  have /eqP := congr1 (cfdotr chi) b0; rewrite b10 scale0r addr0 /= cfdot0l.
  rewrite cfdotZl mulf_eq0 cfdotC cfdot_subr ocp subr0 -cfdotC cfnorm_eq0.
  by rewrite (negbTE nzc) orbF.
have nc: '[chi] = \sum_(a <- R chi) '[X, a].
  transitivity '[S0`_0, S0`_1].
    rewrite [p in _ = p]cfdotC cfdot_subl !cfdot_subr ocp oc'p.
    by rewrite (oSS _ _ Sc') // !subr0 -cfdotC.
  rewrite -iso_t1 ?mem_vchar ?mem_nth // defXY t1cc' tcc'.
  rewrite cfdot_subl {2}big_seq !cfdot_sumr [s in - s]big1 ?subr0 // => a Ra.
  by rewrite (orthogonalP oYR) // inE.
have zXa a: a \in R chi -> isIntC '[X, a].
  by move=> Ra; rewrite cfdot_vchar_Int ?(ZR a) // (vchar_trans ZR ZX).
have defX := orthonormal_span onR (vchar_span ZX).
have nX: '[X] = \sum_(a <- R chi) '[X, a] ^+ 2.
  rewrite big_seq {2}defX cfdot_sumr big_seq.
  by apply: eq_bigr => a Ra; rewrite cfdotZr (eqP (isIntC_Real _)) ?zXa.
pose is01X a (c := '[X, a]) := c == (c != 0)%:R.
have leXa a: a \in R chi -> '[X, a] <= '[X, a] ^+ 2 ?= iff is01X a.
  move=> Ra; rewrite /leCif /is01X (eqP (zXa a Ra)); case: getIntC => [b [|n]].
    by rewrite expr2 !mulr0 !eqxx leC_refl.
  rewrite mulr_sign; case: b.
    rewrite sqrrN -natr_exp oppr_eq0 -(eqN_eqC _ 0) !(eq_sym (- _)) -!addr_eq0.
    by rewrite -leC_sub opprK -!natr_add posC_nat -!(eqN_eqC _ 0) ?addnS.
  rewrite -natr_exp -leq_leC -!eqN_eqC -neq0N_neqC -{1 3}[n.+1]mul1n.
  by rewrite eq_sym leq_pmul2r // eqn_pmul2r.
have{nc nX} part_a: '[chi] <= '[X] ?= iff all is01X (R chi).
  rewrite /leCif nc nX -big_all !big_seq.
  elim/big_rec3: _ => [|a _ u v Ra [le_uv <-]]; first by rewrite leC_refl eqxx.
  rewrite leC_add ?leXa // eq_sym -subr_eq0 addrAC oppr_add addrA addrAC -addrA.
  by rewrite (eq_sym v) posC_add_eq0 ?subr_eq0 ?leC_sub ?leXa // eq_sym leXa.
split=> [|le_psi_Y]; first by case: part_a.
have: '[X] - '[chi] + ('[Y] - '[psi]) == 0.
  rewrite -addrA (addrCA (- _)) -oppr_add addrA subr_eq0; apply/eqP.
  transitivity '[X - Y].
    rewrite cfnorm_sub {5 6}defX cfdot_suml.
    rewrite big_seq big1 ?rmorph0 ?add0r ?subr0 // => a Ra.
    by rewrite cfdotC cfdotZr mulrC (orthogonalP oYR) ?mul0r ?rmorph0 ?inE.
  rewrite -defXY iso_t1 ?mem_vchar ?mem_head // cfnorm_sub ocp rmorph0.
  by rewrite add0r subr0.
rewrite posC_add_eq0 ?leC_sub ?part_a // !subr_eq0 => /andP[nX nY].
split; try exact/eqP; exists (filter [pred a | '[X, a] != 0] (R chi)).
  exact: filter_subseq.
rewrite big_filter big_mkcond /= {1}defX !big_seq; apply: eq_bigr => a Ra.
have [-> | nzXa] := altP eqP; first by rewrite scale0r.
by rewrite eq_sym part_a in nX; rewrite (eqP (allP nX _ Ra)) nzXa scale1r.
Qed.

(* This is Peterfalvi (5.5). *)
Lemma coherent_sum_subseq chi (tau1 : {linear 'CF(L) -> 'CF(G)}) :
    chi \in S ->
    {in 'Z[chi :: chi^*%CF], isometry tau1, to 'Z[irr G]} ->
    tau1 (chi - chi^*%CF) = tau (chi - chi^*%CF) ->
  exists2 E, subseq E (R chi) & tau1 chi = \sum_(a <- E) a.
Proof.
set S1 := (chi :: _) => Schi [iso_t1 Zt1] t1cc'.
have freeS1: free S1.
  have [[_ nrS ccS] _ oS _ _] := cohS.
  by rewrite orthogonal_free ?(conjC_pair_orthogonal ccS).
have subS01: {subset 'Z[chi - 0 :: chi - chi^*%CF] <= 'Z[S1]}.
  apply: vchar_trans setT _; apply/allP; rewrite subr0 /= andbT.
  by rewrite sub_vchar !mem_vchar ?inE ?eqxx ?orbT.
have Zt1c: tau1 (chi - 0) \in 'Z[irr G].
  by rewrite subr0 Zt1 ?mem_vchar ?mem_head.
have [X [Y defXY]] := subcoherent_split Schi Zt1c.
case/subcoherent_norm: (defXY); last 2 [by []].
- by rewrite /orthogonal /= !cfdot0r eqxx Schi cfun0_vchar.
- by split; [apply: sub_in2 iso_t1 | apply: sub_in1 Zt1].
move=> _ [|_ /eqP]; rewrite cfdot0l ?cfnorm_posC // cfnorm_eq0 => /eqP Y0.
case=> E sER defX; exists E => //; rewrite -defX -[X]subr0 -Y0 -[chi]subr0.
by case: defXY.
Qed.

(* This is Peterfalvi (5.6). *)
Lemma extend_coherent S1 xi1 chi :
    [/\ uniq S1, {subset S1 <= S} & conjC_closed S1] -> 
    [&& xi1 \in S1, chi \in S & chi \notin S1] ->
    [/\ (*a*) coherent S1 L^# tau,
        (*b*) isNatC (chi 1%g / xi1 1%g)
      & (*c*) 2%:R * chi 1%g * xi1 1%g < \sum_(xi <- S1) xi 1%g ^+ 2 / '[xi]]
  -> coherent (chi :: chi^*%CF :: S1) L^# tau.
Proof.
move=> [uniqS1 sS1S ccS1] /and3P[S1xi1 Schi notS1chi].
case=> [[t1 [iso_t1 Zt1] eq_t1_tau] /isNatCP[a def_a] ub_chi1].
have [[/allP N_S nrS ccS] [iso_tau Ztau] oS R_P oR] := cohS.
have [ZRchi onRchi sumRchi] := R_P _ Schi.
have ocS1 xi: xi \in S1 -> '[chi, xi] = 0.
  move=> S1xi; have [_ -> //] := pairwise_orthogonalP oS; first exact: sS1S.
  by apply: contraNneq notS1chi => ->.
have /andP[/memPn/= nzS _] := oS.
have oS1: pairwise_orthogonal S1 by exact: sub_pairwise_orthogonal oS.
have [freeS freeS1] := (orthogonal_free oS, orthogonal_free oS1).
have nz_nS1 xi: xi \in S1 -> '[xi] != 0 by rewrite cfnorm_eq0 => /sS1S/nzS.
have nz_xi11: xi1 1%g != 0 by rewrite char1_eq0 ?N_S ?nzS ?sS1S.
have inj_t1: {in 'Z[S1] &, injective t1} := Zisometry_inj iso_t1.
have Z_S1: {subset S1 <= 'Z[S1]} by move=> xi /mem_vchar->.
have inj_t1_S1: {in S1 &, injective t1} := sub_in2 Z_S1 inj_t1.
pose a_ t1xi := S1`_(index t1xi (map t1 S1)) 1%g / xi1 1%g / '[t1xi].
have a_E xi: xi \in S1 -> a_ (t1 xi) = xi 1%g / xi1 1%g / '[xi].
  by move=> S1xi; rewrite /a_ nth_index_map // iso_t1 ?Z_S1.
have a_xi1 : a_ (t1 xi1) = '[xi1]^-1 by rewrite a_E // -mulrA mulVKf //.
have Zachi: chi - a%:R *: xi1 \in 'Z[S, L^#].
  rewrite vcharD1E !cfunE -{2}def_a divfK // subrr eqxx.
  by rewrite scaler_nat sub_vchar ?muln_vchar // mem_vchar // sS1S.
have Zt1achi := vcharW (Ztau _ Zachi).
have [X [Y defXY]] := subcoherent_split Schi Zt1achi.
have [eqXY ZX oYRchi] := defXY.
have ot1S1: pairwise_orthogonal (map t1 S1).
  have{oS1 uniqS1} [uniqS1 oS1] := pairwise_orthogonalP oS1.
  apply/pairwise_orthogonalP; split=> [|_ _ /mapP[u S1u ->] /mapP[v S1v ->]].
     rewrite -(linear0 t1) -map_cons map_inj_in_uniq //.
     by apply: sub_in2 inj_t1 => xi /predU1P[|/Z_S1] -> //; exact: cfun0_vchar.
  by rewrite (inj_in_eq inj_t1_S1) ?iso_t1 ?Z_S1 // => /oS1->.
pose X1 := map t1 (in_tuple S1).
have N_S1_1 xi: xi \in S1 -> isNatC (xi 1%g) by move/sS1S/N_S/char1_Nat.
have oRchiX1 psi: psi \in 'Z[R chi] -> orthogonal psi X1.
  move=> /vchar_span Rc_psi; apply/allP=> _ /predU1P[-> | //].
  apply/allP=> _ /mapP[xi S1xi ->] /=.
  have S1xic := ccS1 _ S1xi.
  have oRcx: orthogonal (R chi) (R xi).
    by rewrite oR // ?sS1S /orthogonal //= !ocS1 ?eqxx //=.
  rewrite (span_orthogonal oRcx) ?subr0 //.
  have [||E sERxi ->] := @coherent_sum_subseq _ t1 (sS1S _ S1xi).
  - have sxiS1: {subset 'Z[xi :: xi^*%CF] <= 'Z[S1]}.
      by apply: vchar_subset => //; exact/allP/and3P.
    by split; [exact: sub_in2 iso_t1 | exact: sub_in1 Zt1].
  - rewrite eq_t1_tau // vchar_split cfunD1E !cfunE isNatC_conj ?N_S1_1 //.
    by rewrite subrr eqxx sub_vchar ?Z_S1.
  by rewrite big_seq memv_suml // => theta /(mem_subseq sERxi)/memv_span.
have [lam Zlam [Z oZS1 defY]]:
  exists2 lam, isIntC lam & exists2 Z : 'CF(G), orthogonal Z (map t1 S1) &
    Y = a%:R *: t1 xi1 - lam *: (\sum_(xi <- X1) a_ xi *: xi) + Z.
- pose lam := a%:R * '[xi1] - '[Y, t1 xi1]; exists lam.
    rewrite isIntC_add ?mulr_natl ?isIntC_opp //.
      by rewrite isIntCE isNatC_muln // cfdot_char_Nat ?N_S ?sS1S.
    rewrite cfdot_vchar_Int ?Zt1 ?Z_S1 // -(subrK X Y) -oppr_sub -eqXY addrC.
    by rewrite sub_vchar // (vchar_trans ZRchi).
  set Z' := _ - _; exists (Y - Z'); last by rewrite addrC subrK.
  have oXt1 xi: xi \in S1 -> '[Y, t1 xi] = - '[X - Y, t1 xi].
    move=> S1xi; rewrite cfdot_subl oppr_sub.
    by rewrite (orthogonalP (oRchiX1 X ZX) X) ?subr0 ?mem_head ?map_f.
  apply/orthogonalP=> _ _ /predU1P[-> | //] /mapP[xi S1xi ->].
  rewrite !cfdot_subl !cfdotZl iso_t1 ?mem_vchar //.
  rewrite cfproj_sum_orthogonal ?map_f // a_E // iso_t1 ?Z_S1 //.
  apply: (mulIf nz_xi11); rewrite divfK ?nz_nS1 // 2!mulr_subl mulrA divfK //.
  rewrite mul0r mulr_subl oppr_sub -addrA addrCA addrC !addrA !oXt1 // !mulNr.
  rewrite -(isNatC_conj (N_S1_1 _ S1xi)) -(isNatC_conj (N_S1_1 _ S1xi1)).
  rewrite opprK [- _ + _]addrC -!(mulrC _^*) -!cfdotZr -cfdot_subr -!linearZ.
  rewrite -linear_sub; set beta : 'CF(L) := _ - _.
  have Zbeta: beta \in 'Z[S1, L^#].
    rewrite vchar_split cfunD1E !cfunE mulrC subrr eqxx.
    by rewrite sub_vchar ?scale_vchar ?Z_S1 // isIntCE N_S1_1.
  rewrite -eqXY eq_t1_tau // iso_tau // ?(vchar_subset _ sS1S) //.
  rewrite cfdot_subl !cfdot_subr !cfdotZr !ocS1 // !mulr0 subrr add0r !cfdotZl.
  by rewrite oppr_sub addrAC subrK subrr.
have [|| leXchi defX] := subcoherent_norm _ _ (erefl _) defXY.
- rewrite Schi {1}scaler_nat muln_vchar ?char_vchar ?N_S ?sS1S //.
  rewrite /orthogonal /= !cfdotZr ocS1 // cfdotC -cfdot_conjC cfConjCK.
  by rewrite cfdotC ocS1 ?rmorph0 ?mulr0 ?eqxx // ccS1.
- set V3 := 'Z[_]; suffices sV3: {subset V3 <= 'Z[S, L^#]}.
    by split; [exact: sub_in2 iso_tau | move=> theta /sV3/Ztau/vcharW].
  move=> _ /vchar_expansion[z Zz ->]; rewrite big_cons big_seq1.
  rewrite add_vchar ?scale_vchar // vcharD1E sub_vchar ?mem_vchar ?ccS //=.
  by rewrite !cfunE isNatC_conj ?subrr // char1_Nat ?N_S.
have{defY leXchi lam Z Zlam oZS1 ub_chi1} defY: Y = a%:R *: t1 xi1.
  have nXY: '[X] + '[Y] = '[chi] + '[a%:R *: xi1].
    rewrite -!cfnorm_subd ?cfdotZr ?ocS1 ?mulr0 // -?eqXY ?iso_tau //.
    rewrite cfdotC (span_orthogonal oYRchi _ (vchar_span ZX)) ?rmorph0 //.
    by rewrite memv_span ?mem_head.
  have{leXchi nXY}: '[Y] <= a%:R ^+ 2 * '[xi1].
    by rewrite -(leC_add2l '[X]) nXY cfnormZ normC_pos ?posC_nat ?leC_add2r.
  rewrite defY cfnormDd; last first.
    rewrite cfdotC (span_orthogonal oZS1) ?rmorph0 //.
      by rewrite memv_span ?mem_head.
    rewrite big_seq memv_sub ?memvZl ?memv_suml ?memv_span ?map_f //.
    by move=> theta S1theta; rewrite memvZl ?memv_span.
  rewrite -leC_sub cfnorm_sub cfnormZ normC_pos ?posC_nat // iso_t1 ?Z_S1 //.
  rewrite -2!addrA (oppr_add (_ * _)) addNKr cfnormZ int_normCK // posC_opp.
  rewrite cfnorm_sum_orthogonal //; set sum_a := \sum_(xi <- _) _.
  rewrite -cfdotC cfdotC cfdotZl cfdotZr cfproj_sum_orthogonal ?map_f // a_xi1.
  rewrite iso_t1 ?Z_S1 // 3!rmorphM !rmorph_nat fmorphV isIntC_conj //.
  rewrite !posC_conjK ?cfnorm_posC // -mulr2n 2!mulrA divfK ?nz_nS1 //.
  rewrite -mulr_natl addrA mulrCA -natr_mul mul2n => ub_lam.
  have [lam0 | nz_lam] := eqVneq lam 0.
    suffices /eqP->: Z == 0 by rewrite lam0 scale0r subr0 addr0.
    rewrite -cfnorm_eq0 eqC_leC cfnorm_posC andbT.
    by rewrite lam0 -mulrA !mul0r subrr add0r in ub_lam.
  set d := \sum_(xi <- _) _ in ub_chi1; pose b := 2%:R * chi 1%g * xi1 1%g / d.
  have pos_S1_1 := posC_isNatC (char1_Nat (N_S _ (sS1S _ _))).
  have xi11_gt0: 0 < xi1 1%g by rewrite ltCE nz_xi11 pos_S1_1.
  have d_gt0: 0 < d.
    have a_xi_ge0 xi: xi \in S1 -> 0 <= xi 1%g ^+ 2 / '[xi].
      by move/pos_S1_1 => xi_1_pos; rewrite 2?posC_mul // posC_inv cfnorm_posC.
    rewrite [d]big_seq; case defS1: {1 2}S1 S1xi1 => // [xi S1'] _.
    have{defS1} S1xi: xi \in S1 by rewrite defS1 mem_head.
    rewrite big_cons S1xi sposC_addr ?posC_sum // ltCE a_xi_ge0 //=.
    by rewrite !mulf_neq0 ?invr_eq0 ?char1_eq0 -?cfnorm_eq0 ?nz_nS1 ?N_S ?sS1S.
  have nz_d: d != 0 by rewrite eqC_leC ltC_geF.
  have b_gt0: 0 < b.
    rewrite !sposC_mul ?sposC_inv -?(ltn_ltC 0 2) // ltCE.
    by rewrite posC_isNatC ?char1_Nat ?char1_eq0 ?N_S // nzS.
  have{ub_chi1} b_lt1: b < 1.
    rewrite ltCE eqC_leC -(leC_pmul2r 1 b d_gt0) -(leC_pmul2r b 1 d_gt0).
    by rewrite -eqC_leC -ltCE mul1r divfK.
  have{ub_lam} ub_lam: lam ^+ 2 <= b * lam.
    rewrite -(leC_pmul2r _ _ d_gt0) (mulrAC b) divfK //.
    rewrite -[d](divfK (mulf_neq0 nz_xi11 nz_xi11)) -[chi _](divfK nz_xi11).
    rewrite def_a 4!mulrA 2!(mulrAC _ _ lam) 2?leC_pmul2r //.
    rewrite -natr_mul mul2n -mulrA.
    have ->: d / xi1 1%g ^+ 2 = sum_a.
      rewrite big_distrl /sum_a big_map !big_seq; apply: eq_bigr => xi S1xi /=.
      rewrite a_E // iso_t1 ?Z_S1 //= normC_pos; last first.
        by rewrite !(cfnorm_posC, posC_mul, posC_inv) ?pos_S1_1.
      rewrite mulrAC 2!exprn_mull -!expr_inv [p in p * '[xi]]mulrA.
      by rewrite divfK ?nz_nS1.
    rewrite -leC_sub -oppr_sub posC_opp (leC_trans _ ub_lam) //.
    by rewrite (mulrC lam) -{1}[_ - _]addr0 leC_add2l cfnorm_posC.
  have lam_gt0: 0 < lam.
    rewrite ltCE nz_lam -(leC_pmul2l _ _ b_gt0) mulr0.
    by apply: leC_trans ub_lam; rewrite -int_normCK // posC_mul ?posC_norm.
  rewrite leC_pmul2r // ltC_geF // in ub_lam.
  rewrite (ltC_leC_trans b_lt1) //; have:= lam_gt0.
  have /isNatCP[n ->]: isNatC lam by rewrite isNatC_posInt Zlam ltCW.
  by rewrite -(ltn_ltC 0) -(leq_leC 1).
have [uniqRchi dotRchi] := orthonormalP onRchi.
have{defX} [|nX _ [E sERchi defX]] := defX.
  by rewrite defY !cfnormZ iso_t1 ?Z_S1 ?leC_refl.
have{sERchi} defE: E = filter (mem E) (R chi) by exact/subseq_uniqP.
pose Ec := filter [predC E] (R chi); pose Xc := - \sum_(xi <- Ec) xi.
have def_XXc: X - Xc = tau (chi - chi^*%CF).
  rewrite opprK defX -big_cat sumRchi; apply: eq_big_perm.
  by rewrite defE perm_filterC.
have oXXc: '[X, Xc] = 0.
  rewrite cfdotNr defX defE !big_filter big_seq_cond cfdot_suml.
  rewrite big1 ?oppr0 // => b1 /andP[Rb1 Eb1].
  rewrite big_seq_cond cfdot_sumr big1 // => b2 /andP[Rb2 notEb2].
  by rewrite dotRchi // [_ == _](contraNF _ notEb2) // => /eqP <-.
have [neq_cc' Sc'] := (hasPn nrS _ Schi, ccS _ Schi).
have occ': '[chi, chi^*] = 0.
  by have [_ -> //] := pairwise_orthogonalP oS; rewrite eq_sym.
have Zcc': chi - chi^*%CF \in 'Z[S, L^#].
  rewrite vchar_split cfunD1E sub_vchar ?mem_vchar //= !cfunE subr_eq0.
  by rewrite isNatC_conj // char1_Nat ?N_S.
have nXc: '[Xc] = '[chi^*].
  by apply: (addrI '[X]); rewrite {2}nX -!cfnorm_subd // def_XXc iso_tau.
have ZXc: Xc \in 'Z[R chi].
  rewrite opp_vchar big_filter big_seq_cond sum_vchar // => b1 /andP[Rb1 _].
  by rewrite mem_vchar ?orthonormal_free.
pose X3 := [tuple of X :: Xc :: X1].
pose S3 := [tuple of chi :: chi^*%CF :: in_tuple S1]; rewrite-[_ :: _]/(val S3).
have oX3: pairwise_orthogonal X3.
  rewrite /= (pairwise_orthogonal_cat (X :: Xc)) orthogonal_cons !oRchiX1 //.
  rewrite ot1S1 /pairwise_orthogonal /= !inE oXXc eqxx !andbT !(eq_sym 0).
  by rewrite -!cfnorm_eq0 nX nXc cfnorm_conjC orbb cfnorm_eq0 nzS.
have sS3S: {subset S3 <= S} by apply/allP; rewrite /= Schi Sc'; exact/allP.
have uniqS3: uniq S3.
  rewrite /= inE negb_or eq_sym neq_cc' notS1chi (contra _ notS1chi) //.
  by move/ccS1; rewrite cfConjCK.
have oS3: pairwise_orthogonal S3 by exact: sub_pairwise_orthogonal oS.
have nX3: map cfnorm X3 = map cfnorm S3.
  rewrite /= nX nXc -map_comp; congr [:: _, _ & _].
  by apply: eq_in_map => xi /= S1xi; rewrite iso_t1 ?Z_S1.
have Z_X3: {subset X3 <= 'Z[irr G]}.
  apply/allP; rewrite /= !(vchar_trans ZRchi) //.
  by apply/allP=> _ /mapP[xi S1xi ->]; rewrite Zt1 ?Z_S1. 
have [t3 defX3 iso_t3] := Zisometry_of_cfnorm oS3 oX3 nX3 Z_X3.
have [t3chi t3chi' t3S1] := defX3; rewrite -/(map t3 _) in t3S1.
exists t3 => // psi; rewrite vchar_split cfunD1E => /andP[].
case/vchar_expansion=> z Zz ->; rewrite !big_cons; set z2 := z _; set z3 := z _.
rewrite 2!linearD !linearZ t3chi t3chi'.
rewrite -(subrK chi chi^*%CF) -(addrC chi) scaler_addr !addrA -scaler_addl.
rewrite -{1 4}(subrK (a%:R *: xi1) chi) scaler_addr addrAC addrC -!addrA.
rewrite -oppr_sub 3!cfunE (cfun_on0 (vchar_on Zcc')) ?inE ?eqxx // oppr0 mulr0.
rewrite 2!cfunE (cfun_on0 (vchar_on Zachi)) ?inE ?eqxx // mulr0 !add0r => ph10.
rewrite 2!(linearD tau) 2!(linearZ tau) (linearN tau) -def_XXc oppr_sub.
rewrite eqXY defY !scaler_subr addrCA -!addrA; congr (_ + _).
rewrite addrCA addrA -scaler_subl addrK; congr (_ + _).
rewrite -eq_t1_tau; last first.
  rewrite vchar_split cfunD1E {1}scaler_addl /z2 /z3.
  rewrite !add_vchar // ?scale_vchar ?isIntC_nat //; try exact: Z_S1.
  by rewrite big_seq sum_vchar // => xi S1xi; rewrite scale_vchar ?Z_S1.
rewrite (linearD t1) !(linearZ t1) addKr !linear_sum (big_nth 0).
rewrite [r in _ = r](big_nth 0) !big_mkord; apply: eq_bigr => /= i _.
by rewrite !linearZ; congr (_ *: _); rewrite -(nth_map _ 0) // t3S1 (nth_map 0).
Qed.

(* This is Peterfalvi (5.7). *)
(* This is almost a superset of (1.4): we could use it to get a coherent      *)
(* isometry, which would necessarily map irreducibles to signed irreducibles. *)
(* It would then only remain to show that the signs are chosen consistently,  *)
(* by considering the degrees of the differences.                             *)
Lemma uniform_degree_coherence :
  constant [seq (chi : 'CF(L)) 1%g | chi <- S] -> coherent S L^# tau.
Proof.
case defS: {1}S => /= [|chi S1] szS; first by rewrite defS; exact: nil_coherent.
have{szS} unifS xi: xi \in S -> xi 1%g = chi 1%g.
  by rewrite defS => /predU1P[-> // | S'xi]; apply/eqP/(allP szS)/map_f.
have Schi: chi \in S by rewrite defS mem_head.
have [[/allP N_S nrS ccS] IZtau oS R_P oR] := cohS; have [Itau Ztau] := IZtau.
have freeS := orthogonal_free oS; have /mem_vchar Z_S := freeS.
have Zd: {in S &, forall xi1 xi2, xi1 - xi2 \in 'Z[S, L^#]}.
  move=> xi1 xi2 Sxi1 Sxi2 /=.
  by rewrite vcharD1E sub_vchar ?Z_S //= !cfunE !unifS ?subrr.
have [neq_chic Schic] := (hasPn nrS _ Schi, ccS _ Schi).
have [/andP[/memPn notS0 _] ooS] := pairwise_orthogonalP oS.
pose S' xi := [predD1 S & xi]; pose S'c xi := predD1 (S' xi) xi^*%CF.
have{oR} oR xi1 xi2: xi1 \in S -> xi2 \in S'c xi1 -> orthogonal (R xi1) (R xi2).
  move=> Sxi1 /and3P[/= neq_xi21c neq_xi21 Sxi2].
  by rewrite orthogonal_sym oR // /orthogonal /= !ooS ?eqxx // ccS.
have oSc xi: xi \in S -> '[xi, xi^*] = 0.
  by move=> Sxi; rewrite ooS ?ccS // -[_ == _]negbK eq_sym (hasPn nrS).
pose D xi := tau (chi - xi).
have Z_D xi: xi \in S -> D xi \in 'Z[irr G] by move/(Zd _ _ Schi)/Ztau/vcharW.
have /isNatCP[N defN]: isNatC '[chi] by rewrite cfdot_char_Nat ?N_S.
have dotD: {in S' chi &, forall xi1 xi2, '[D xi1, D xi2] = N%:R + '[xi1, xi2]}.
- move=> xi1 xi2 /andP[ne_xi1chi Sxi1] /andP[ne_xi2chi Sxi2].
  rewrite Itau ?Zd // cfdot_subl !cfdot_subr defN.
  by rewrite 2?ooS // 1?eq_sym // oppr_sub !subr0.
have /R_P[ZRchi onRchi defRchi] := Schi; have frRchi := orthonormal_free onRchi.
have szRchi: size (R chi) = (N + N)%N.
  apply: (can_inj getNatC_nat); rewrite -cfnorm_orthonormal // -defRchi.
  by rewrite dotD ?inE ?ccS ?(hasPn nrS) // cfnorm_conjC defN -natr_add.
pose sub_Rchi X := exists2 E, subseq E (R chi) & X = \sum_(a <- E) a.
pose Xspec X := [/\ X \in 'Z[R chi], '[X]_G = N%:R & sub_Rchi X].
pose Xi_spec X xi := X - D xi \in 'Z[R xi] /\ '[X, D xi] = N%:R.
have haveX xi: xi \in S'c chi -> exists2 X, Xspec X & Xi_spec X xi.
  move=> S'xi; have /and3P[/= ne_xi_chi' ne_xi_chi Sxi] := S'xi.
  have [neq_xi' Sxi'] := (hasPn nrS xi Sxi, ccS xi Sxi).
  have [X [Y1 defXY1]] := subcoherent_split Schi (Z_D _ Sxi).
  have [eqXY1 RchiX oY1chi] := defXY1; have sRchiX := vchar_span RchiX.
  have Z_Y1: Y1 \in 'Z[irr G].
    rewrite -[Y1](subrK X) -oppr_sub -eqXY1 addrC sub_vchar ?Z_D //.
    exact: (vchar_trans ZRchi).
  have [X1 [Y defX1Y]] := subcoherent_split Sxi Z_Y1; pose Y2 := X + Y.
  have [eqX1Y RxiX1 oYxi] := defX1Y; pose D2 := tau (xi - chi).
  have defX1Y2: [/\ D2 = X1 - Y2, X1 \in 'Z[R xi] & orthogonal Y2 (R xi)].
    rewrite -oppr_sub -addrA -oppr_sub -eqX1Y -eqXY1 -linearN oppr_sub.
    split=> //; apply/orthogonalP=> _ a /predU1P[-> | //] Rxi_a.
    rewrite cfdotDl (span_orthogonal (oR _ _ _ S'xi)) ?(memv_span Rxi_a) //.
    by rewrite add0r (orthogonalP oYxi) ?mem_head.
  have [||minX eqX1] := subcoherent_norm _ _ (erefl _) defXY1.
  - by rewrite char_vchar ?N_S /orthogonal //= !ooS ?eqxx // eq_sym.
  - apply: sub_iso_to IZtau; last exact: vcharW.
    by apply: vchar_trans_on; apply/allP; rewrite /= !Zd.
  have [||minX1 _]:= subcoherent_norm _ _ (erefl _) defX1Y2.
  - rewrite char_vchar ?N_S /orthogonal //= !ooS ?eqxx //.
    by rewrite (inv_eq (@cfConjCK _ _)).
  - apply: sub_iso_to IZtau; last exact: vcharW.
    by apply: vchar_trans_on; apply/allP; rewrite /= !Zd.
  have span_head := memv_span (mem_head _ _); have sRxiX1 := vchar_span RxiX1.
  have Y0: Y = 0.
    apply/eqP; rewrite -cfnorm_eq0 eqC_leC cfnorm_posC andbT.
    rewrite -(leC_add2l ('[X] + '[X1])) -!addrA.
    rewrite -2?cfnorm_subd -?eqX1Y -?eqXY1 ?addr0; first last.
    - by rewrite cfdotC (span_orthogonal oYxi) ?rmorph0 ?span_head.
    - by rewrite cfdotC (span_orthogonal oY1chi) ?rmorph0 ?span_head.
    by rewrite dotD ?inE ?ne_xi_chi // -defN leC_add.
  rewrite eqX1Y Y0 subr0 defN in eqX1.
  have [nX _ defX] := eqX1 minX1; exists X => //; red.
  rewrite eqXY1 eqX1Y Y0 subr0 oppr_add opprK addNKr cfdot_subr nX.
  by rewrite (span_orthogonal (oR _ _ _ S'xi)) ?subr0 ?(vchar_span RxiX1).
pose X_spec X := forall xi, X - D xi \in 'Z[irr G] /\ '[X, D xi] = N%:R.
have [X [RchiX nX defX] X_S'c]: exists2 X, Xspec X & {in S'c chi, X_spec X}.
  have [S_chi | /allPn[xi1 Sxi1]] := altP (@allP _ (pred2 chi chi^*%CF) S).
    pose E := take N (R chi); pose Ec := drop N (R chi).
    have eqRchi: E ++ Ec = R chi by rewrite cat_take_drop.
    have:= onRchi; rewrite -eqRchi orthonormal_cat => /and3P[onE onEc oEEc].
    exists (\sum_(a <- E) a) => [|xi /and3P[? ? /S_chi/norP[] //]].
    split; last by exists E; rewrite // -[E]cats0 -eqRchi cat_subseq ?sub0seq.
      rewrite big_seq sum_vchar // => a Ea.
      by rewrite mem_vchar // -eqRchi mem_cat Ea.
    by rewrite cfnorm_orthonormal //= size_takel ?szRchi ?leq_addl.
  case/norP=> ne_xi1chi ne_xi1chi'; have S'xi1: xi1 \in S'c chi by exact/and3P.
  have [X [RchiX nX defX] [Rxi1X1 XD_N]] := haveX _ S'xi1.
  exists X => // xi S'xi; have [ne_xi_chi' ne_xi_chi /= Sxi] := and3P S'xi.
  have /R_P[ZRxi _ _] := Sxi; have /R_P[ZRxi1 _ defRxi1] := Sxi1.
  have [-> | ne_xi_xi1] := eqVneq xi xi1; first by rewrite (vchar_trans ZRxi1).
  have [sRchiX sRxi1X1] := (vchar_span RchiX, vchar_span Rxi1X1).
  have [-> | ne_xi_xi1'] := eqVneq xi xi1^*%CF.
    rewrite /D -[chi](subrK xi1) -addrA linearD cfdotDr XD_N oppr_add addrA.
    rewrite defRxi1 big_seq (span_orthogonal (oR _ _ _ S'xi1)) ?addr0 //.
      by rewrite sub_vchar ?sum_vchar // (vchar_trans ZRxi1).
    by rewrite memv_suml // => a /memv_span.
  have [X' [RchiX' nX' _] [RxiX' X'D_N]] := haveX _ S'xi.
  have [ZXi sRxiX'] := (vchar_trans ZRxi RxiX', vchar_span RxiX').
  suffices: '[X - X'] == 0 by rewrite cfnorm_eq0 subr_eq0 => /eqP->.
  rewrite cfnorm_sub subr_eq0 nX nX' isIntC_conj -?mulr2n; last first.
    by rewrite cfdot_vchar_Int ?(vchar_trans ZRchi).
  apply/eqP; congr (_ *+ _); transitivity '[D xi1, D xi].
    by rewrite dotD ?inE ?ne_xi_chi ?ne_xi1chi ?ooS ?addr0 // eq_sym.
  rewrite -[D xi](subrK X') -oppr_sub addrC -[D _](subrK X) -oppr_sub addrC.
  rewrite cfdot_subr cfdot_subl -addrA addrC -addrA addrCA cfdot_subl oppr_sub.
  rewrite (span_orthogonal (oR xi1 xi _ _)) //; last exact/and3P.
  rewrite (span_orthogonal (oR chi xi _ _)) // subrr add0r.
  rewrite cfdotC (span_orthogonal (oR chi xi1 _ _)) ?rmorph0 ?oppr0 ?add0r //.
  exact: (vchar_span RchiX').
have ZX: X \in 'Z[irr G] := vchar_trans ZRchi RchiX.
have{defX X_S'c} X_S': {in S' chi, X_spec X}.
  move=> xi.
  have [-> _| ne_xi_chi' S'xi] := eqVneq xi chi^*%CF; last exact/X_S'c/andP.
  rewrite /D defRchi {1}big_seq sub_vchar ?sum_vchar //.
  have{defX} [E sER defX] := defX; pose Ec := filter [predC E] (R chi).
  have eqRchi: perm_eq (R chi) (E ++ Ec).
    by rewrite -(perm_filterC (mem E)) -(subseq_uniqP _ _) ?uniq_free.
  have:= onRchi; rewrite (eq_orthonormal eqRchi) orthonormal_cat.
  case/and3P=> onE _ oEEc.
  rewrite (eq_big_perm _ eqRchi) big_cat /= -defX cfdotDr nX defX !big_seq.
  by rewrite (span_orthogonal oEEc) ?addr0 // memv_suml // => ? /memv_span.
pose X_ xi := X - D xi.
have X_chi: X_ chi = X by rewrite /X_ /D subrr linear0 subr0.
have ZX_ xi: xi \in S -> X_ xi \in 'Z[irr G].
  have [-> _ | ne_xi_chi Sxi] := eqVneq xi chi; first by rewrite X_chi.
  by have [|//] := X_S' xi; exact/andP.
have{X_S'} X_iso: {in S &, isometry X_}.
  have dotXD_N xi: xi \in S' chi -> '[X, D xi] = N%:R by case/X_S'.
  move=> xi1 xi2; have [-> _ | ne_xi1_chi Sxi1] := eqVneq xi1 chi.
    have [-> _ | S'xi2 Sxi2] := eqVneq xi2 chi; first by rewrite X_chi nX.
    by rewrite X_chi cfdot_subr nX dotXD_N ?inE ?S'xi2 // subrr ooS // eq_sym.
  have S'xi1: xi1 \in S' chi by exact/andP.
  have [-> _ | ne_xi2_chi Sxi2] := eqVneq xi2 chi.
    by rewrite X_chi cfdot_subl nX cfdotC dotXD_N // conjC_nat subrr ooS.
  have S'xi2: xi2 \in S' chi by exact/andP.
  rewrite cfdot_subl !cfdot_subr nX (cfdotC _ X) !dotXD_N // conjC_nat.
  by rewrite oppr_sub subrr add0r dotD // addrC addKr.
pose XS := map X_ S.
have ZXS: {subset XS <= 'Z[irr G]} by move=> _ /mapP[xi Sxi ->]; exact: ZX_.
have oXS: pairwise_orthogonal XS.
  apply/pairwise_orthogonalP.
  split=> [|_ _ /mapP[xi1 Sxi1 ->] /mapP[xi2 Sxi2 ->] neq_xi12]; last first.
    by rewrite X_iso // ooS //; apply: contraNneq neq_xi12 => ->.
  rewrite /=; apply/andP; split.
    apply/mapP=> [[xi Sxi /eqP/idPn[]]]; rewrite eq_sym -cfnorm_eq0 X_iso //.
    by rewrite cfnorm_eq0 notS0.
  rewrite map_inj_in_uniq ?uniq_free // => xi1 xi2 Sx1 Sx2 /= /addrI/eqP.
  rewrite -addr_eq0 addrC -linear_sub addrAC oppr_add addNKr opprK.
  by rewrite -cfnorm_eq0 Itau ?Zd // cfnorm_eq0 subr_eq0 => /eqP.
have nXS: map cfnorm XS = map cfnorm S.
  by rewrite -map_comp; apply: eq_in_map => xi Sxi; rewrite /= X_iso.
have [tau1 defXS It1] := Zisometry_of_cfnorm oS oXS nXS ZXS.
have tau1S: {in S, tau1 =1 X_}.
  move=> xi Sxi; rewrite -(nth_index 0 Sxi).
  by rewrite -(nth_map _ 0) ?index_mem // defXS (nth_map 0) ?index_mem.
exists tau1 => // xi; rewrite vcharD1E => /andP[/vchar_expansion[z Zz ->]]{xi}.
rewrite defS big_cons /= !cfunE addr_eq0 => eq_z.
have{eq_z} ->: z chi = - \sum_(xi <- S1) z xi.
  have nz_chi1: chi 1%g != 0 by rewrite char1_eq0 ?N_S // notS0.
  apply: (mulIf nz_chi1); rewrite (eqP eq_z) sum_cfunE mulNr -mulr_suml.
  rewrite !big_seq; congr (- _); apply: eq_bigr => xi S1xi.
  by rewrite cfunE unifS // defS !inE S1xi orbT.
rewrite scaleNr scaler_suml addrC -oppr_sub -sumr_sub !linearN !linear_sum /=.
apply: eq_big_seq => xi S1xi; rewrite -scaler_subr !linearZ /= -/(D _).
congr (_ *: - _); rewrite linear_sub !tau1S // ?defS 1?mem_behead //.
by rewrite X_chi oppr_add addNKr opprK.
Qed.

End SubCoherentProperties.

Section DadeAut.

Variables (L G : {group gT}) (A : {set gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha).

Section DadeAutIrr.

Variable u : {rmorphism algC -> algC}.
Local Notation "alpha ^u" := (cfAut u alpha).

(* This is Peterfalvi (5.9)(a). *)
Lemma cfAut_Dade_ext calS (tau1 : {additive 'CF(L) -> 'CF(G)}) chi : 
    (1 < size calS)%N -> uniq calS -> {subset calS <= irr L} ->
    'Z[calS, L^#] =i 'Z[calS, A] -> {in calS, forall f, f^u \in calS} ->
    {in 'Z[calS], isometry tau1, to 'Z[irr G]} ->
    {in 'Z[calS, A], forall f, tau1 f = f^\tau} ->
    chi \in calS ->
  (tau1 chi)^u = tau1 (chi^u).
Proof.
move=> S_gt1 uniqS irrS defZA sSuS [Itau1 Ztau1] tau1_tau Schi.
have orthS := sub_orthonormal irrS uniqS (irr_orthonormal L).
have{orthS} [freeS [_ orthS]] := (orthonormal_free orthS, orthonormalP orthS).
have sSZS: {subset calS <= 'Z[calS]} by move=> phi Sphi; exact: mem_vchar.
have natS1 psi: psi \in calS -> exists2 a, (a > 0)%N & psi 1%g = a%:R.
  case/irrS/irrP=> i ->; have /isNatCP[a def_a] := isNatC_irr1 i.
  by exists a; rewrite // ltn_ltC -def_a ltC_irr1.
have /natS1[a a_gt0 chi1] := Schi; rewrite ltn_ltC in a_gt0.
pose mu b psi := b%:R *: chi - a%:R *: psi.
have ZAmu b psi: psi \in calS -> psi 1%g = b%:R -> mu b psi \in 'Z[calS, A].
  move=> Spsi psi1; rewrite -defZA vcharD1E !cfunE chi1 psi1 mulrC subrr.
  by rewrite sub_vchar //= scale_vchar ?sSZS ?isIntC_nat.
have{orthS} Npsi psi (Spsi : psi \in calS): '[tau1 psi] = 1%:R.
  by rewrite Itau1 ?sSZS // orthS ?eqxx.
have{Npsi} def_tau1 Spsi := vchar_norm1P (Ztau1 _ (sSZS _ Spsi)) (Npsi _ Spsi).
have [eps [i tau1_chi]] := def_tau1 _ Schi; set e := (-1) ^+ eps in tau1_chi.
have{def_tau1} def_tau1 psi: psi \in calS -> exists j, tau1 psi = e *: 'chi_j.
  move=> Spsi; have [/natS1[b _ psi1] /def_tau1[f [j tau1psi]]] := (Spsi, Spsi).
  suffices: 0 <= (e *: tau1 psi) 1%g.
    rewrite tau1psi; have [-> | neq_f_eps] := eqVneq f eps; first by exists j.
    rewrite scalerA -signr_addb scaler_sign addbC -negb_eqb neq_f_eps.
    by rewrite cfunE posC_opp ltC_geF ?ltC_irr1.
  rewrite -(posC_mulr _ a_gt0) cfunE mulrCA.
  have: tau1 (mu b psi) 1%g == 0 by rewrite tau1_tau ?ZAmu ?Dade1.
  rewrite raddf_sub !scaler_nat 2!raddfMn -!scaler_nat tau1_chi !cfunE subr_eq0.
  by move/eqP <-; rewrite -(mulrCA e) signrMK posC_mull ?posC_nat ?ltC_irr1.
have [psi Spsi neq_chi_psi]: exists2 psi, psi \in calS & chi != psi.
  have [m [|psi S] defS] := rot_to Schi.
    by move: S_gt1; rewrite -(size_rot m) defS.
  exists psi; first by rewrite -(mem_rot m) defS !inE eqxx orbT.
  by move: uniqS; rewrite -(rot_uniq m) defS => /andP[/norP[]].
have /natS1[b b_gt0 psi1] := Spsi.
have: (tau1 (mu b psi))^u == tau1 (mu b psi)^u.
  by rewrite !tau1_tau ?cfAut_vchar ?ZAmu ?Dade_aut.
rewrite !raddf_sub [-%R]lock !raddfZnat /= -lock.
have [/sSuS/def_tau1[iu ->] /sSuS/def_tau1[ju ->]] := (Schi, Spsi).
have: (tau1 chi)^u != (tau1 psi)^u.
  rewrite (inj_eq (@cfAut_inj _ _ _)).
  by rewrite (inj_in_eq (isometry_inj Itau1 (@sub_vchar _ _ _ _))) ?sSZS.
have /def_tau1[j ->] := Spsi; rewrite tau1_chi !cfAutZ_Int ?isIntC_sign //.
rewrite !scalerA -!(mulrC e) -!scalerA -!scaler_subr -!aut_IirrE.
rewrite !(inj_eq (scalerI _)) ?signr_eq0 // (inj_eq chi_inj).
by rewrite eq_subZnat_irr eqn0Ngt b_gt0 orbC => /negPf-> /= /andP[/eqP-> _].
Qed.

End DadeAutIrr.

(* This is Peterfalvi (5.9)(b). *)
Lemma Dade_irr_sub_conjC i (chi := 'chi_i) (phi := chi - chi^*%CF):
  chi \in 'CF(L, 1%g |: A) -> exists t, phi^\tau = 'chi_t - ('chi_t)^*%CF.
Proof.
have [Rchi | notRchi Achi] := eqVneq (conjC_Iirr i) i.
  by exists 0; rewrite chi0_1 cfConjC1 /phi -conjC_IirrE Rchi !subrr linear0.
have Zphi: phi \in 'Z[irr L, A].
  have notA1: 1%g \notin A by have [/subsetD1P[]] := ddA.
  by rewrite -(setU1K notA1) sub_conjC_vchar // vchar_split irr_vchar.
have Zphi_tau: phi^\tau \in 'Z[irr G, G^#].
  by rewrite vchar_split Dade_cfun Dade_vchar ?Zphi.
have norm_phi_tau : '[phi^\tau] = 2%:R.
  rewrite Dade_isometry ?(vchar_on Zphi) // cfnorm_sub -conjC_IirrE.
  by rewrite !cfdot_irr !eqxx eq_sym (negPf notRchi) rmorph0 addr0 subr0.
have [j [k [ne_kj phi_tau]]] := vchar_norm2 Zphi_tau norm_phi_tau.
suffices def_k: conjC_Iirr j = k by exists j; rewrite -conjC_IirrE def_k.
have/esym:= eq_subZnat_irr 1 1 k j (conjC_Iirr j) (conjC_Iirr k).
rewrite (negPf ne_kj) orbF /= !scale1r !conjC_IirrE -rmorph_sub.
rewrite -oppr_sub -phi_tau /= Dade_conjC // rmorph_sub /= cfConjCK.
by rewrite -linearN oppr_sub eqxx => /andP[/eqP->].
Qed.

End DadeAut.

End Five.
