(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg matrix poly finset.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor center gproduct cyclic pgroup abelian frobenius.
Require Import mxalgebra mxrepresentation vector falgebra fieldext galois.
Require Import ssrnum rat algC algnum classfun character.
Require Import integral_char inertia vcharacter.
Require Import PFsection1 PFsection2.

(******************************************************************************)
(* This file covers Peterfalvi, Section 3: TI-Subsets with Cyclic Normalizers *)
(******************************************************************************)
(* Given a direct product decomposition defW : W1 \x W2 = W, we define here:  *)
(*       cyclicTIset defW == the set complement of W1 and W2 in W; this       *)
(*            (locally) V    definition is usually Let-bound to V.            *)
(*                        := W :\: (W1 :|: W2).                               *)
(* cyclicTI_hypothesis G defW <-> W is a cyclic of odd order that is the      *)
(*                           normaliser in G of its non-empty TI subset       *)
(*                           V = cyclicTIset defW = W :\: (W1 :|: W2).        *)
(*   -> This is Peterfalvi, Hypothesis (3.1), or Feit-Thompson (13.1).        *)
(*   cyclicTIirr defW i j == the irreducible character of W coinciding with   *)
(*       (locally) w_ i j    chi_i and 'chi_j on W1 and W2, respectively.     *)
(*                           This notation is usually Let-bound to w_ i j.    *)
(*                        := 'chi_(dprod_Iirr defW (i, j)).                   *)
(* cfCyclicTIset defW i j == the virtual character of 'Z[irr W, V] coinciding *)
(*    (locally) alpha_ i j   with 1 - chi_i and 1 - 'chi_j on W1 and W2,      *)
(*                           respectively. This definition is denoted by      *)
(*                           alpha_ i j in this file, and is only used in the *)
(*                           proof if Peterfalvi (13.9) in the sequel.        *)
(*                        := cfDprod defW (1 - 'chi_i) (1 - 'chi_j).          *)
(*                           = 1 - w_ i 0 - w_ 0 j + w_ i j.                  *)
(* cfCyclicTIsetBase defW := the tuple of all the alpha_ i j, for i, j != 0.  *)
(*     (locally) cfWVbase    This is a basis of 'CF(W, V); this definition is *)
(*                           not used outside this file.                      *)
(* For ctiW : cyclicTI_hypothesis defW G we also define                       *)
(*       cyclicTIiso ctiW == a linear isometry from 'CF(W) to 'CF(G) that     *)
(*        (locally) sigma    that extends induction on 'CF(W, V), maps the    *)
(*                           w_ i j to virtual characters, and w_ 0 0 to 1.   *)
(*                           This definition is usually Let-bound to sigma,   *)
(*                           and only depends extensionally on W, V and G.    *)
(*     (locally) eta_ i j := sigma (w_ i j), as in sections 13 and 14 of      *)
(*                           tha Peterfalv text.                              *)
(*   cyclicTI_NC ctiW phi == the number of eta_ i j constituents of phi.      *)
(*       (locally) NC phi := #|[set ij | '[phi, eta_ ij .1 ij.2] != 0]|.      *)
(* The construction of sigma involves other technical definitions, which are  *)
(* only mentioned in techincal lemmas and should not be used outside this     *)
(* file:                                                                      *)
(*      dcTIirr ctiW i j  == the index of a normal virtual character of G,    *)
(*                           such that for all i, j != 0 we have              *)
(*                           beta_ i j = - x_ i 0 - x_ 0 j + x_ i j, where    *)
(*    (locally) beta_ i j := 'Ind[G] (alpha_ i j) - 1.                        *)
(*      (locally) x_ i j  := dchi (dcTIirr ctiW i j).                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Definitions.

Variables (gT : finGroupType) (G W W1 W2 : {set gT}).

Definition cyclicTIset of W1 \x W2 = W := W :\: (W1 :|: W2).

Definition cyclicTI_hypothesis (defW : W1 \x W2 = W) (V := cyclicTIset defW) :=
  [/\ cyclic W, odd #|W|, V != set0 & normedTI V G W].

End Definitions.

(* These is defined as a Notation which clients can bind with a Section Let   *)
(* that can be folded easily. *)
Notation cyclicTIirr defW i j := 'chi_(dprod_Iirr defW (i, j)).

Section Proofs.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).
Hypothesis defW : W1 \x W2 = W.

Let V := cyclicTIset defW.
Let w_ i j := cyclicTIirr defW i j.
Let w1 := #|W1|.
Let w2 := #|W2|.

Lemma cyclicTIirrC (defW21 : W2 \x W1 = W) i j :
  cyclicTIirr defW21 j i = w_ i j.
Proof. by rewrite (dprod_IirrC defW21 defW). Qed.

Lemma cycTIirrP chi : chi \in irr W -> {i : Iirr W1 & {j | chi = w_ i j}}.
Proof.
case/irrP/sig_eqW=> k ->{chi}.
by have /codomP/sig_eqW[[i j] ->] := dprod_Iirr_onto defW k; exists i, j.
Qed.

Lemma cycTIirr_aut u i j : w_ (aut_Iirr u i) (aut_Iirr u j) = cfAut u (w_ i j).
Proof. by rewrite /w_ !dprod_IirrE cfAutDprod !aut_IirrE. Qed.

Let sW1W : W1 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.
Let sW2W : W2 \subset W. Proof. by have /mulG_sub[] := dprodW defW. Qed.

Lemma card_cycTIset : #|V| = (w1.-1 * w2.-1)%N.
Proof.
have [_ _ _ tiW12] := dprodP defW.
rewrite cardsD (setIidPr _) ?subUset ?sW1W // cardsU {}tiW12 cards1.
rewrite -(dprod_card defW) -addnBA // -!subn1 -/w1 -/w2 subnDA.
by rewrite mulnBl mulnBr mul1n muln1.
Qed.

Definition cfCyclicTIset i j := cfDprod defW (1 - 'chi_i) (1 - 'chi_j).
Local Notation alpha_ := cfCyclicTIset.

Lemma cycTIirr00 : w_ 0 0 = 1. Proof. by rewrite /w_ dprod_Iirr0 irr0. Qed.
Local Notation w_00 := cycTIirr00.

Lemma cycTIirr_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof. by rewrite /w_ !dprod_IirrE !irr0 cfDprod_split. Qed.

Lemma cfker_cycTIl j : W1 \subset cfker (w_ 0 j).
Proof. by rewrite /w_ dprod_IirrE irr0 cfDprod_cfun1l cfker_sdprod. Qed.

Lemma cfker_cycTIr i : W2 \subset cfker (w_ i 0).
Proof. by rewrite /w_ dprod_IirrE irr0 cfDprod_cfun1r cfker_sdprod. Qed.

Let cfdot_w i1 j1 i2 j2 : '[w_ i1 j1, w_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
Proof. exact: cfdot_dprod_irr. Qed.

Lemma cfCycTI_E i j : alpha_ i j = 1 - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite -w_00 -[w_ i j]opprK /w_ !dprod_IirrE !irr0 -addrA -opprD -!mulrBl.
by rewrite -mulrBr -!rmorphB.
Qed.
Local Notation alphaE := cfCycTI_E.

Lemma cfCycTI_vchar i j : alpha_ i j \in 'Z[irr W].
Proof. by rewrite alphaE rpredD ?rpredB ?rpred1 ?irr_vchar. Qed.

Definition cfCyclicTIsetBase :=
  [seq alpha_ ij.1 ij.2 | ij in setX [set~ 0] [set~ 0]].
Local Notation cfWVbase := cfCyclicTIsetBase.

Let cfdot_alpha_w i1 j1 i2 j2 :
  i2 != 0 -> j2 != 0 -> '[alpha_ i1 j1, w_ i2 j2] = [&& i1 == i2 & j1 == j2]%:R.
Proof.
move=> nzi2 nzj2; rewrite alphaE -w_00 !cfdotDl !cfdotNl !cfdot_w.
by rewrite !(eq_sym 0) (negPf nzi2) (negPf nzj2) /= andbF !subr0 add0r.
Qed.

Let cfdot_alpha_1 i j : i != 0 -> j != 0 -> '[alpha_ i j, 1] = 1.
Proof.
move=> nzi nzj; rewrite alphaE -w_00 !cfdotDl !cfdotNl !cfdot_w.
by rewrite !eqxx andbT /= (negPf nzi) (negPf nzj) addr0 !subr0.
Qed.

Let cfnorm_alpha i j : i != 0 -> j != 0 -> '[alpha_ i j] = 4%:R.
Proof.
move=> nzi nzj; rewrite -[4]/(size [:: 1; - w_ i 0; - w_ 0 j; w_ i j]).
rewrite -cfnorm_orthonormal 3?big_cons ?big_seq1 ?addrA -?alphaE //.
rewrite /orthonormal -w_00 /= !cfdotNl !cfdotNr !opprK !oppr_eq0 !cfnorm_irr.
by rewrite !cfdot_w !eqxx /= !(eq_sym 0) (negPf nzi) (negPf nzj) !eqxx.
Qed.

Lemma cfCycTIbase_free : free cfWVbase.
Proof.
apply/freeP=> s /= s_alpha_0 ij; case def_ij: (enum_val ij) => [i j].
have /andP[nzi nzj]: (i != 0) && (j != 0).
  by rewrite -!in_setC1 -in_setX -def_ij enum_valP.
have:= congr1 (cfdotr (w_ i j)) s_alpha_0; rewrite raddf_sum raddf0 => <-.
rewrite (bigD1 ij) //= nth_image def_ij cfdotZl cfdot_alpha_w // !eqxx mulr1.
rewrite big1 ?addr0 // => ij1; rewrite nth_image -(inj_eq enum_val_inj) def_ij.
case: (enum_val ij1) => i1 j1 /= => ne_ij1_ij.
by rewrite cfdotZl cfdot_alpha_w // mulr_natr mulrb ifN.
Qed.

(* Further results on alpha_ depend on the assumption that W is cyclic. *)

Hypothesis ctiW : cyclicTI_hypothesis G defW.

Let cycW : cyclic W. Proof. by case: ctiW. Qed.
Let oddW : odd #|W|. Proof. by case: ctiW. Qed.
Let ntV : V != set0. Proof. by case: ctiW. Qed.
Let tiV : normedTI V G W. Proof. by case: ctiW. Qed.

Lemma cyclicTIhyp_sym (defW21 : W2 \x W1 = W) : cyclicTI_hypothesis G defW21.
Proof. by split; rewrite // /cyclicTIset setUC. Qed.

Let cycW1 : cyclic W1. Proof. exact: cyclicS cycW. Qed.
Let cycW2 : cyclic W2. Proof. exact: cyclicS cycW. Qed.
Let coW12 : coprime w1 w2. Proof. by rewrite -(cyclic_dprod defW). Qed.

Let Wlin k : 'chi[W]_k \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W1lin i : 'chi[W1]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let W2lin i : 'chi[W2]_i \is a linear_char. Proof. exact/irr_cyclic_lin. Qed.
Let w_lin i j : w_ i j \is a linear_char. Proof. exact: Wlin. Qed.

Let nirrW1 : #|Iirr W1| = w1. Proof. exact: card_Iirr_cyclic. Qed.
Let nirrW2 : #|Iirr W2| = w2. Proof. exact: card_Iirr_cyclic. Qed.
Let NirrW1 : Nirr W1 = w1. Proof. by rewrite -nirrW1 card_ord. Qed.
Let NirrW2 : Nirr W2 = w2. Proof. by rewrite -nirrW2 card_ord. Qed.

Lemma cycTI_nontrivial : W1 :!=: 1%g /\ W2 :!=: 1%g.
Proof.
apply/andP; rewrite -!cardG_gt1 -!(subn_gt0 1) !subn1 -muln_gt0.
by rewrite -card_cycTIset card_gt0.
Qed.

Let ntW1 : W1 :!=: 1%g. Proof. by case: cycTI_nontrivial. Qed.
Let ntW2 : W2 :!=: 1%g. Proof. by case: cycTI_nontrivial. Qed.
Let oddW1 : odd w1. Proof. exact: oddSg oddW. Qed.
Let oddW2 : odd w2. Proof. exact: oddSg oddW. Qed.
Let w1gt2 : (2 < w1)%N. Proof. by rewrite odd_gt2 ?cardG_gt1. Qed.
Let w2gt2 : (2 < w2)%N. Proof. by rewrite odd_gt2 ?cardG_gt1. Qed.

Let neq_w12 : w1 != w2.
Proof.
by apply: contraTneq coW12 => ->; rewrite /coprime gcdnn -(subnKC w2gt2).
Qed.

Let cWW : abelian W. Proof. exact: cyclic_abelian. Qed.
Let nsVW : V <| W. Proof. by rewrite -sub_abelian_normal ?subsetDl. Qed.
Let sWG : W \subset G. Proof. by have [|_ /subsetIP[]] := normedTI_P _ tiV. Qed.
Let sVG : V \subset G^#. Proof. by rewrite setDSS ?subsetU ?sub1G. Qed.

Let alpha1 i j : alpha_ i j 1%g = 0.
Proof. by rewrite cfDprod1 !cfunE cfun11 lin_char1 // subrr mul0r. Qed.

(* This first part of Peterfalvi (3.4) will be used in (4.10) and (13.9). *)
Lemma cfCycTI_on i j : alpha_ i j \in 'CF(W, V).
Proof.
apply/cfun_onP=> x; rewrite !inE negb_and negbK orbC.
case/or3P => [/cfun0->// | W1x | W2x].
  by rewrite -[x]mulg1 cfDprodE // !cfunE cfun11 lin_char1 ?subrr ?mulr0.
by rewrite -[x]mul1g cfDprodE // !cfunE cfun11 lin_char1 ?subrr ?mul0r.
Qed.

(* This is Peterfalvi (3.4). *)
Lemma cfCycTIbase_basis : basis_of 'CF(W, V) cfWVbase.
Proof.
rewrite basisEfree cfCycTIbase_free /=.
have ->: \dim 'CF(W, V) = #|V| by rewrite dim_cfun_on_abelian ?subsetDl.
rewrite size_tuple cardsX !cardsC1 nirrW1 nirrW2 -card_cycTIset leqnn andbT.
by apply/span_subvP=> _ /imageP[[i j] _ ->]; apply: cfCycTI_on.
Qed.
Local Notation cfWVbasis := cfCycTIbase_basis.

(* We need to prove (3.5) first in order to define sigma and prove (3.2). *)

Let beta_ i j : 'CF(G) := 'Ind[G] (alpha_ i j) - 1.

Let beta1 i j : beta_ i j 1%g = -1.
Proof. by rewrite !cfunE cfun11 cfInd1 // alpha1 mulr0 add0r. Qed.

Let beta_vchar i j : beta_ i j \in 'Z[irr G].
Proof. by rewrite rpredB ?rpred1 ?cfInd_vchar ?cfCycTI_vchar. Qed.

Let cfdot_Ind_alpha_1 i j :
  i != 0 -> j != 0 -> '['Ind[G] (alpha_ i j), 1] = 1.
Proof. by move=> nz_i nz_j; rewrite -cfdot_Res_r rmorph1 cfdot_alpha_1. Qed.

(* This is the first equation of Peterfalvi (3.5.1). *)
Let cfdot_beta_1 i j : i != 0 -> j != 0 -> '[beta_ i j, 1] = 0.
Proof.
by move=> nzi nzj; rewrite cfdotBl cfdot_Ind_alpha_1 // cfnorm1 subrr.
Qed.

(* These are the other equations of Peterfalvi (3.5.1). *)
Let cfdot_beta i1 j1 i2 j2 :
    i1 != 0 -> j1 != 0 -> i2 != 0 -> j2 != 0 -> 
  '[beta_ i1 j1, beta_ i2 j2] = ((i1 == i2).+1 * (j1 == j2).+1).-1%:R.
Proof.
move=> nzi1 nzj1 nzi2 nzj2; rewrite mulSnr addnS mulnSr /=.
rewrite cfdotBr cfdot_beta_1 // subr0 cfdotBl (cfdotC 1) cfdot_Ind_alpha_1 //.
rewrite (normedTI_isometry _ tiV) ?cfCycTI_on // rmorph1 addrC.
rewrite (alphaE i2) cfdotDr !cfdotBr cfdot_alpha_1 // -!addrA addKr addrA addrC.
rewrite cfdot_alpha_w // -addnA !natrD mulnb; congr (_ + _).
rewrite alphaE -w_00 !(cfdotBl, cfdotDl) !cfdot_w !eqxx !(eq_sym 0).
rewrite (negPf nzi1) (negPf nzj1) (negPf nzi2) (negPf nzj2) /= !andbF !andbT /=.
by rewrite !(addr0, opprB, oppr0) add0r.
Qed.

Let cfnorm_beta i j : i != 0 -> j != 0 -> '[beta_ i j] = 3%:R.
Proof. by move=> nzi nzj; rewrite cfdot_beta // !eqxx. Qed.

Local Notation A_ i j := (dirr_constt (beta_ i j)).
Local Notation nA_ i j := (dirr_constt (- beta_ i j)).
Local Notation specA nzi nzj :=
  (dirr_small_norm (beta_vchar _ _) (cfnorm_beta nzi nzj) isT).

Let card_dirr_const_beta_diff i1 j1 i2 j2 :
    i1 != 0 -> j1 != 0 -> i2 != 0 -> j2 != 0 -> i1 != i2 -> j1 != j2 -> 
  #|A_ i1 j1 :&: A_ i2 j2| = #|A_ i1 j1 :&: nA_ i2 j2|.
Proof.
move=> nzi1 nzj1 nzi2 nzj2 i2'1 j2'1.
apply/eqP; rewrite -eqC_nat -subr_eq0 -cfdot_sum_dchi.
have [[_ _ <-] [_ _ <-]] := (specA nzi1 nzj1, specA nzi2 nzj2).
by rewrite cfdot_beta // (negPf i2'1) (negPf j2'1).
Qed.

(* This is the symmetrical part of (3.5.2). *)
Let card_dirr_const_beta_difflr i1 i2 j1 j2 :
    i1 != 0 -> i2 != 0 -> j1 != 0 -> j2 != 0 ->
    '[beta_ i1 j1, beta_ i2 j2] = 1 ->
  #|A_ i1 j1 :&: A_ i2 j2| = 1%N /\ #|A_ i1 j1 :&: nA_ i2 j2| = 0%N.
Proof.
move=> nzi1 nzi2 nzj1 nzj2 /eqP.
have [[oA _ sA] [oB _ sB]] := (specA nzi1 nzj1, specA nzi2 nzj2).
do [set A := A_ i1 j1; set B := A_ i2 j2; set C := nA_ i2 j2] in oA oB sA sB *.
rewrite sA sB cfdot_sum_dchi -/A -/B -/C subr_eq -mulrS eqr_nat => /eqP.
have [-> | /=[u /setIP[Au Bu]]] := set_0Vmem (A :&: B); first by rewrite cards0.
have [-> | /=[v /setIP[Av Cv]]] := set_0Vmem (A :&: C); first by rewrite cards0.
rewrite (cardsD1 u) [#|A :&: C|](cardsD1 v) !in_setI Au Bu Av Cv !add1n; case.
suffices ->: A :&: B :\ u = set0 by rewrite cards0.
apply/eqP/set0Pn=> [[w /setD1P[u'w /setIP[Aw Bw]]]].
have Bnv: ndirr v \in B by rewrite -dirr_constt_oppr.
have{sA} Db1: beta_ i1 j1 = dchi w + dchi u + dchi v.
  have B'v: v \notin B by rewrite -[v]ndirrK dirr_constt_oppl.
  have [v'u v'w] := (memPn B'v u Bu, memPn B'v w Bw).
  have Uwuv: uniq [:: w; u; v] by rewrite /= !inE negb_or u'w v'u v'w.
  rewrite sA; transitivity (\sum_(x in [:: w; u; v]) dchi x); last first.
    by rewrite -big_uniq //= 2!big_cons big_seq1 addrA.
  apply/esym/eq_bigl/subset_cardP; first by rewrite oA (card_uniqP Uwuv).
  by apply/subsetP/allP; rewrite /= Au Av Aw.
have{sB} Db2: beta_ i2 j2 = dchi w + dchi u - dchi v.
  have A'nv: ndirr v \notin A by rewrite dirr_constt_oppl.
  have [nv'u nv'w] := (memPn A'nv u Au, memPn A'nv w Aw).
  have Uwunv: uniq [:: w; u; ndirr v] by rewrite /= !inE negb_or u'w nv'u nv'w.
  rewrite sB; transitivity (\sum_(x in [:: w; u; ndirr v]) dchi x); last first.
    by rewrite -big_uniq //= 2!big_cons big_seq1 dchi_ndirrE addrA.
  apply/esym/eq_bigl/subset_cardP; first by rewrite oB (card_uniqP Uwunv).
  by apply/subsetP/allP; rewrite /= Bu Bnv Bw.
have /eqP/idPn[]: (2%:R *: dchi v) 1%g = (beta_ i1 j1 - beta_ i2 j2) 1%g.
  by rewrite Db2 opprB addrC -addrA Db1 addKr scaler_nat.
by rewrite !(beta1, cfunE) subrr !mulf_eq0 pnatr_eq0 signr_eq0 irr1_neq0.
Qed.

(* This is the vertical instance of step (3.5.2). *)
Let card_dirr_const_beta_diffr i j1 j2 :
    i != 0 -> j1 != 0 -> j2 != 0 -> j1 != j2 -> 
  #|A_ i j1 :&: A_ i j2| = 1%N /\ #|A_ i j1 :&: nA_ i j2| = 0%N.
Proof.
move=> nzi nzj1 nzj2 j2'1; apply: card_dirr_const_beta_difflr => //.
by rewrite cfdot_beta // !eqxx (negPf j2'1).
Qed.

(* This is the horizontal instance of step (3.5.2). *)
Let card_dirr_const_beta_diffl i1 i2 j :
    i1 != 0 -> i2 != 0 -> j != 0 -> i1 != i2 -> 
  #|A_ i1 j :&: A_ i2 j| = 1%N /\ #|A_ i1 j :&: nA_ i2 j| = 0%N.
Proof.
move=> nzi1 nzi2 nzj i2'1; apply: card_dirr_const_beta_difflr => //.
by rewrite cfdot_beta // !eqxx (negPf i2'1).
Qed.

Lemma dirr_const_beta_inv i j v1 v2 v3 :
     i != 0 -> j != 0 -> beta_ i j = dchi v1 + dchi v2 + dchi v3 ->
   A_ i j = [set v1; v2; v3].
Proof.
move=> nzi nzj Db; apply/eqP; have [oA _ sumA] := specA nzi nzj.
rewrite eqEcard {}oA !cardsU !cards1 !(leq_subLR, addn1, addnS, ltnS) andbT.
apply/subsetP=> v; rewrite !inE Db !cfdotDl !cfdot_dchi !(eq_sym v).
by do 3![case: (_ =P v) => // _]; rewrite !sub0r -!opprD -!natrD oppr_gt0 ltrn0.
Qed.

Section BetaDecomposition.

Section SymmetricalDecomposition.

Variables W'1 W'2 : {group gT}.
Variable beta : Iirr W'1 -> Iirr W'2 -> 'CF(G).

Local Notation pA i j := (dirr_constt (beta i j)).
Local Notation nA i j := (dirr_constt (- beta i j)).
Local Notation dA i j v1 v2 v3 :=  
     [&& i != 0, j != 0 & pA i j == [set v1; v2; v3]].

Definition beta_hyp3_5 :=
  [/\ odd (Nirr W'1), (2 < Nirr W'1)%N, (2 < Nirr W'2)%N
    & forall i j i' j', i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> 
        [/\ #| pA i j | = 3, pA i j :&: nA i j = set0,
             i != i' -> j != j' ->  
             #|pA i j :&: pA i' j'| = #|pA i j :&: nA i' j'|,
             i != i' -> 
               #|pA i j :&: pA i' j| = 1%N /\ #|pA i j :&: nA i' j| = 0%N &
             j != j' -> 
               #|pA i j :&: pA i j'| = 1%N /\ #|pA i j :&: nA i j'| = 0%N]].

Hypothesis beta_hyp : beta_hyp3_5.

Let Oddw'1 : odd (Nirr W'1). Proof. by case: beta_hyp. Qed.
Let H2Lw'1 : (2 < Nirr W'1)%N. Proof. by case: beta_hyp. Qed.
Let H2Lw'2 : (2 < Nirr W'2)%N. Proof. by case: beta_hyp. Qed.
Let beta_diff := let: And4 _ _ _ beta_diff := beta_hyp in beta_diff.

Local Notation "v1 '<> v2" := ((v1 != v2) && (v1 != ndirr v2)) (at level 10).

Fact dAsl i j v1 v2 v3 : dA i j v1 v2 v3 -> dA i j v2 v1 v3.
Proof. by congr [&& _, _ & _ == _]; rewrite [[set v1; v2]]setUC. Qed.

Fact dAsr i j v1 v2 v3 : dA i j v1 v2 v3 -> dA i j v1 v3 v2.
Proof. by congr [&& _, _ & _ == _]; rewrite setUAC. Qed.

Fact dAr i j v1 v2 v3 : dA i j v1 v2 v3 -> dA i j v3 v1 v2.
Proof. by move/dAsr/dAsl. Qed.

Fact dAE i j : i != 0 -> j != 0 -> {v | dA i j v.1.1 v.1.2 v.2}.
Proof.
move=> NZi NZj.
pose v := odflt (dirr1 _, dirr1 _, dirr1 _) [pick v | dA i j v.1.1 v.1.2 v.2].
exists v; rewrite /v; case: pickP => //=.
rewrite NZi NZj /=.
case: (beta_diff NZi NZj NZi NZj)=> HH _ _ _ _.
move/eqP: HH.
case: (set_0Vmem (pA i j))=> [-> //| [u1 U1iPa]]; first by rewrite cards0.
rewrite (cardsD1 u1) U1iPa.
set A1 := _  :\: _; case: (set_0Vmem A1)=> [-> //| [u2 U2iA1]].
  by rewrite cards0.
rewrite (cardsD1 u2) U2iA1.
set A2 := _  :\: _; case: (set_0Vmem A2)=> [-> //| [u3 U3iA2]].
  by rewrite cards0.
rewrite (cardsD1 u3) U3iA2.
set A3 := _  :\: _; case: (set_0Vmem A3)=> [A3i0 _ |[u4 U4iA3]]; last first.
  by rewrite (cardsD1 u4) U4iA3.
move=> /(_ (u1,u2,u3)) /idP [] /=.
rewrite -(setD1K U1iPa) -/A1 -(setD1K U2iA1) -/A2 -(setD1K U3iA2) -/A3 A3i0.
by rewrite setU0 setUA.
Qed.

Fact dA_in i j v1 v2 v3 : dA i j v1 v2 v3 -> v1 \in pA i j.
Proof. by case/and3P=> _ _ /eqP->; rewrite !inE eqxx. Qed.

Fact dA_diff i j v1 v2 v3 : dA i j v1 v2 v3 -> v1 '<> v2.
Proof.
case/and3P=> NZi NZj /eqP pAE.
case: (beta_diff NZi NZj NZi NZj)=> ACard Adiff _ _ _.
apply/andP; split; apply/eqP=> HH; last first.
  move/setP: Adiff=> /(_ v2).
  by rewrite inE dirr_constt_oppr -HH pAE !inE !eqxx ?orbT.
move/eqP: ACard; rewrite pAE HH (cardsD1 v2) 3!inE eqxx /=.
rewrite (cardsD1 v3) 6!inE eqxx orbT.
set A1 := _  :\: _; case: (set_0Vmem A1)=> [-> |[u1]].
  by rewrite cards0; case: (v3 == _).
by rewrite !inE => /and3P [/negPf-> /negPf->].
Qed.

Fact dA_diffs i j v1 v2 v3 : 
  dA i j v1 v2 v3 -> [&& v1 '<> v2, v2 '<> v3 & v1 '<> v3].
Proof.
move=> HB; have HB1 := dAsr HB; have HB2 := dAsr (dAsl HB).
by rewrite !(dA_diff HB, dA_diff HB1, dA_diff HB2).
Qed.
 
Fact dA_in_split i j v1 v2 v3 v : 
  dA i j v1 v2 v3 -> v \in pA i j -> [|| v == v1, v == v2 | v == v3].
Proof. by case/and3P=> _ _ /eqP->; rewrite !inE -!orbA. Qed.

Fact dAEI i j k : i != 0 -> j != 0 -> k \in pA i j -> {v | dA i j k v.1 v.2}.
Proof.
move=> NZi NZj; case: (dAE NZi NZj)=> [[[v1 v2] v3]] /and3P [_ _ /eqP DAE].
rewrite {1}DAE !inE -orbA; case: (boolP (_ == _))=> [/eqP-> _|_].
  by exists (v2,v3); rewrite DAE NZi NZj /=.
case: (boolP (_ == _))=> [/eqP-> _|_].
  by exists (v1,v3); rewrite dAsl // DAE NZi NZj /=.
case: (boolP (_ == _))=> [/eqP-> _|//].
by exists (v1,v2); rewrite dAr // DAE NZi NZj /=.
Qed.

Fact dA2r_diff i j k v1 v2 v3 v4 v5 : 
  j != k -> dA i j v1 v2 v3 -> dA i k v1 v4 v5 -> v2 '<> v4.
Proof.
move=> JdK dA1 dA2; case/andP: (dA_diff dA1)=> V1dV2 V1dNV2.
case/and3P: dA1 => NZi NZj /eqP pAijE; case/and3P: dA2 => _ NZk /eqP pAikE.
case: (beta_diff NZi NZj NZi NZk)=> Card IA _ _ /(_ JdK) [].
rewrite pAijE pAikE => C1 C2. 
apply/andP;split; apply/eqP => HH.
  move: C1; rewrite -HH (cardsD1 v1) !inE eqxx /= (cardsD1 v2) !inE eqxx ?orbT.
  by rewrite eq_sym V1dV2.
move: C2; rewrite (cardsD1 v2) 5!inE eqxx dirr_constt_oppr HH ndirrK !orbT.
by rewrite /= (cardsD1 v4) {1}pAikE !inE eqxx orbT.
Qed.

Fact dA2l_diff i j k v1 v2 v3 v4 v5 :
  j != k ->  dA j i v1 v2 v3 -> dA k i v1 v4 v5 -> v2 '<> v4.
Proof.
move=> JdK dA1 dA2; case/andP: (dA_diff dA1)=> V1dV2 V1dNV2.
case/and3P: dA1 => NZj NZi /eqP pAijE; case/and3P: dA2 => NZk _ /eqP pAikE.
case: (beta_diff NZj NZi NZk NZi)=> Card IA _ /(_ JdK) [].
rewrite pAijE pAikE => C1 C2 _. 
apply/andP;split; apply/eqP => HH.
  move: C1; rewrite -HH (cardsD1 v1) !inE eqxx /= (cardsD1 v2) !inE eqxx ?orbT.
  by rewrite eq_sym V1dV2.
move: C2; rewrite (cardsD1 v2) 5!inE eqxx dirr_constt_oppr HH ndirrK !orbT.
by rewrite /= (cardsD1 v4) {1}pAikE !inE eqxx orbT.
Qed.

Fact dA2l_notin i1 i2 j v1 v2 v3 v4 v5 : 
  i1 != i2 -> dA i1 j v1 v2 v3 -> dA i2 j v1 v4 v5 -> v2 \notin pA i2 j.
Proof.
move=> I1dI2 Ai1j Ai2j; apply/negP.
move/(dA_in_split Ai2j)=> /or3P [] /eqP HH; 
    try (rewrite HH in Ai1j) ; try (rewrite HH in Ai2j).
- by move: (dA_diff Ai1j); rewrite eqxx.
- by move: (dA2l_diff I1dI2 Ai1j Ai2j); rewrite eqxx.
by move: (dA2l_diff I1dI2 Ai1j (dAsr Ai2j)); rewrite eqxx.
Qed.

Fact dA2r_diffs  i j k v1 v2 v3 v4 v5 :
    j != k -> dA i j v1 v2 v3 -> dA i k v1 v4 v5 ->
  [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 & v3 '<> v5].
Proof.
move=> JdK HB HB'; have HB1 := dAsr HB; have HB1' := dAsr HB'.
by rewrite !(dA2r_diff _ HB HB', dA2r_diff _ HB HB1', dA2r_diff _ HB1 HB', 
             dA2r_diff _ HB1 HB1').
Qed.

Fact dA2l_diffs  i j k v1 v2 v3 v4 v5 :
    j != k -> dA j i v1 v2 v3 -> dA k i v1 v4 v5 ->
  [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 &  v3 '<> v5].
Proof.
move=> JdK HB HB'; have HB1 := dAsr HB; have HB1' := dAsr HB'.
by rewrite !(dA2l_diff _ HB HB', dA2l_diff _ HB HB1', dA2l_diff _ HB1 HB', 
             dA2l_diff _ HB1 HB1').
Qed.

Fact dAr_split i j k v1 v2 v3 :  k != 0 -> 
  dA i j v1 v2 v3 -> [|| v1 \in pA i k, v2 \in pA i k | v3 \in pA i k].
Proof.
move=> NZk dAij; case/and3P: (dAij) => NZi NZj /eqP pAijE.
case: (boolP (j == k))=> [/eqP<- | JdK].
  by rewrite pAijE !inE eqxx.
case: (beta_diff NZi NZj NZi NZk)=> Card IA _ _ /(_ JdK) [].
set A := _ :&: _; case: (set_0Vmem A)=> [-> //| [u]]; first by rewrite cards0.
by rewrite inE => 
     /andP [] /(dA_in_split dAij) /or3P [] /eqP-> ->; rewrite ?orbT.
Qed.

Fact dAl_split i j k v1 v2 v3 :  k != 0 -> 
  dA j i v1 v2 v3 -> [|| v1 \in pA k i, v2 \in pA k i | v3 \in pA k i].
Proof.
move=> NZk dAij; case/and3P: (dAij) => NZj NZi /eqP pAijE.
case: (boolP (j == k))=> [/eqP<- | JdK].
  by rewrite pAijE !inE eqxx.
case: (beta_diff NZj NZi NZk NZi)=> Card IA _ /(_ JdK) [].
set A := _ :&: _; case: (set_0Vmem A)=> [-> //| [u]]; first by rewrite cards0.
by rewrite inE =>
     /andP [] /(dA_in_split dAij) /or3P [] /eqP-> ->; rewrite ?orbT.
Qed.

Fact dA2_split i1 j1 i2 j2 v1 v2 v3 v4 v5 : i1 != i2 -> j1 != j2 -> 
    dA i1 j1 v1 v2 v3 -> dA i2 j2 v1 v4 v5 -> 
  [|| (v4 == ndirr v2) && v5 '<> v3, (v4 == ndirr v3) && v5 '<> v2,
      (v5 == ndirr v2) && v4 '<> v3 | (v5 == ndirr v3) && v4 '<> v2].
Proof.
move=> I1dI2 J1dJ2.
wlog: v2 v3 v4 v5 / v4 = ndirr v2.
  move=> IW dAi1j1 dAi2j2.
  case/and3P: (dAi1j1) => NZi1 NZj1 /eqP pAi1j1E.
  case/and3P: (dAi2j2) => NZi2 NZj2 /eqP pAi2j2E.
  case: (beta_diff NZi1 NZj1 NZi2 NZj2)=> Card IA /(_ I1dI2 J1dJ2) HH _ _.
  case: (beta_diff NZi2 NZj2 NZi2 NZj2)=> Card' IA' _ _ _.
  move: HH; set A := _ :&: nA _ _; case: (set_0Vmem A)=> [-> /eqP | [u]].
    by rewrite cards0 pAi1j1E pAi2j2E (cardsD1 v1) 9!{1}inE !eqxx.
  rewrite inE pAi1j1E dirr_constt_oppr pAi2j2E !inE -!orbA.
  case/andP=> /or3P [] /eqP->.
  - by rewrite (negPf (ndirr_diff _)) /= => /orP [] /eqP HH;
       move/setP: IA'=> /(_ v1); rewrite inE dirr_constt_oppr HH pAi2j2E;
       rewrite !inE !eqxx ?orbT.
  - case/or3P => /eqP HH.
    - move/setP: IA=> /(_ v2); rewrite inE dirr_constt_oppr HH pAi1j1E.
      by rewrite !inE !eqxx ?orbT.
    - by move=> _; apply: IW => //.
    by case/or4P: (IW v2 v3 v5 v4 (sym_equal HH) dAi1j1 (dAsr dAi2j2)) 
           => // ->; rewrite ?orbT //.
  case/or3P => /eqP HH.
    - move/setP: IA=> /(_ v3); rewrite inE dirr_constt_oppr HH pAi1j1E.
      by rewrite !inE !eqxx ?orbT.
    - by case/or4P: (IW v3 v2 v4 v5 (sym_equal HH) (dAsr dAi1j1) dAi2j2) 
           => // ->; rewrite ?orbT //.
  by case/or4P: (IW v3 v2 v5 v4 (sym_equal HH) (dAsr dAi1j1) (dAsr dAi2j2)) 
         => // ->; rewrite ?orbT //.
move=> -> dAi1j1 dAi2j2; rewrite eqxx.
case/and3P: (dAi1j1) => NZi1 NZj1 /eqP pAi1j1E.
case/and3P: (dAi2j2) => NZi2 NZj2 /eqP pAi2j2E.
case: (beta_diff NZi1 NZj1 NZi2 NZj2)=> Card IA /(_ I1dI2 J1dJ2) HH _ _.
move/eqP: HH; rewrite pAi1j1E pAi2j2E.
rewrite (cardsD1 v1) !inE eqxx /=.
set A1 := _ :&: nA _ _.
rewrite [#|A1|](cardsD1 v2) inE dirr_constt_oppr pAi2j2E.
rewrite !inE !eqxx ?orbT /=.
case: (boolP (v5 == _))=> [/eqP V5eV3| V5dV3]; last first.
  case: (boolP (v5 == _))=> [/eqP V5eNV3 | //].
  rewrite V5eNV3.
  set A2 := _ :\ v1; case: (set_0Vmem A2) => [->|[u]].
    rewrite cards0 addn0.
    rewrite (cardsD1 v3) 3!inE dirr_constt_oppr pAi2j2E.
    rewrite !inE V5eNV3 !eqxx ?orbT /=.
    by case/andP: (dA_diff (dAr (dAr dAi1j1))); rewrite eq_sym => ->.
  rewrite !inE => /and3P [/negPf->] /= /orP [] /eqP->.
    rewrite eq_sym (negPf (ndirr_diff _)).
    by case/andP: (dA_diff (dAr (dAr dAi1j1))) => _ /negPf->.
  rewrite [v3 == _ v3]eq_sym (negPf (ndirr_diff _)).
  case/andP: (dA_diff (dAr (dAr dAi1j1))).
  by case: (boolP (v3 == _))=> // /eqP ->; rewrite ndirrK eqxx.
rewrite V5eV3 (cardsD1 v3) !inE eqxx ?orbT /=.
case/andP: (dA_diff (dAsr dAi1j1)); rewrite eq_sym => -> _ /=.
set A2 := _ :\  v2; case: (set_0Vmem A2) => [->|[u]].
  by rewrite cards0 addn0.
rewrite 4!inE dirr_constt_oppr pAi2j2E !inE V5eV3.
case/and3P=> HH; case: (boolP (ndirr _ == ndirr _))=> [/eqP|_].
  by move/ndirr_inj=> HH1; case/eqP: HH.
rewrite {HH}(negPf HH) !orbF /= => /orP [] /eqP->.
  rewrite (negPf (ndirr_diff _)) eq_sym.
  by case/andP: (dA_diff (dAr dAi1j1)) => _ /negPf->.
rewrite (negPf (ndirr_diff _)) eq_sym.
by case/andP: (dA_diff (dAsr dAi1j1)) => _ /negPf->.
Qed.

Fact dA2_n_split i1 j1 i2 j2 v1 v2 v3 v4 v5 : i1 != i2 -> j1 != j2 -> 
 dA i1 j1 v1 v2 v3 -> dA i2 j2 (ndirr v1) v4 v5 -> 
 [|| (v4 == v2) && v5 '<> v3, (v4 == v3) && v5 '<> v2,
     (v5 == v2) && v4 '<> v3 | (v5 == v3) && v4 '<> v2].
Proof.
move=> I1dI2 J1dJ2.
wlog: v2 v3 v4 v5 / v4 = v2.
  move=> IW dAi1j1 dAi2j2.
  case/and3P: (dAi1j1) => NZi1 NZj1 /eqP pAi1j1E.
  case/and3P: (dAi2j2) => NZi2 NZj2 /eqP pAi2j2E.
  case: (beta_diff NZi1 NZj1 NZi2 NZj2)=> Card IA /(_ I1dI2 J1dJ2) HH _ _.
  case: (beta_diff NZi2 NZj2 NZi2 NZj2)=> Card' IA' _ _ _.
  move: HH.
  set A := _ :&: nA _ _; rewrite [#|A|](cardsD1 v1) inE dirr_constt_oppr.
  rewrite pAi1j1E pAi2j2E !inE !eqxx /=.
  set A1 := _ :&: _; case: (set_0Vmem A1)=> [-> /eqP | [u]].
    by rewrite cards0.
  rewrite !inE -!orbA.
  case/andP=> /or3P [] /eqP->.
  - rewrite eq_sym (negPf (ndirr_diff _)) /= => /orP [] /eqP HH.
      by case/andP: (dA_diff dAi2j2); rewrite eq_sym HH eqxx.
    by case/andP: (dA_diff (dAsr dAi2j2)); rewrite eq_sym HH eqxx.
  - case/or3P => /eqP HH.
    - by case/andP: (dA_diff dAi1j1); rewrite HH ndirrK eqxx.
    - by case/or4P: (IW v2 v3 v4 v5 (sym_equal HH) dAi1j1 dAi2j2)
           => // ->; rewrite ?orbT.
    by case/or4P: (IW v2 v3 v5 v4 (sym_equal HH) dAi1j1 (dAsr dAi2j2))
           => // ->; rewrite ?orbT.
  case/andP: (dA_diff (dAr dAi1j1))=> _ /negPf -> /= /orP [] /eqP HH.
    by case/or4P: (IW v3 v2 v4 v5 (sym_equal HH) (dAsr dAi1j1) dAi2j2) 
        => // ->; rewrite ?orbT.
  by case/or4P: (IW v3 v2 v5 v4 (sym_equal HH) (dAsr dAi1j1) (dAsr dAi2j2)) 
      => // ->; rewrite ?orbT.
move=> -> dAi1j1 dAi2j2; rewrite eqxx.
case/and3P: (dAi1j1) => NZi1 NZj1 /eqP pAi1j1E.
case/and3P: (dAi2j2) => NZi2 NZj2 /eqP pAi2j2E.
case: (beta_diff NZi1 NZj1 NZi2 NZj2)=> Card IA /(_ I1dI2 J1dJ2) HH _ _.
move/eqP: HH; rewrite pAi1j1E pAi2j2E.
rewrite (cardsD1 v2) !inE eqxx ?orbT /=.
set A1 := _ :&: nA _ _.
rewrite [#|A1|](cardsD1 v1) inE dirr_constt_oppr pAi2j2E.
rewrite !inE !eqxx /=.
case: (boolP (v5 == _))=> [/eqP V5eV3| V5dV3]; last first.
  case: (boolP (v5 == _))=> [/eqP V5eNV3 | //].
  rewrite V5eNV3.
  rewrite [#|_ :\ v1|](cardsD1 v3) 3!inE dirr_constt_oppr pAi2j2E.
  rewrite !inE V5eNV3 !eqxx ?orbT /=.
  case/andP: (dA_diff (dAr dAi1j1)) => -> _ /=.
  set A2 := _ :\ _; case: (set_0Vmem A2) => [->|[u]].
    by rewrite cards0 addn0.
  rewrite !inE => /and3P [/negPf->]; rewrite ?orbF => /= /orP [] /eqP->.
    rewrite eq_sym (negPf (ndirr_diff _)) /=.
    by case/andP: (dA_diff (dAsr dAi1j1)) => _ /negPf->.
  rewrite [v3 == _ v3]eq_sym (negPf (ndirr_diff _)).
  by case/andP: (dA_diff (dAr dAi1j1)) => _ /negPf->.
rewrite V5eV3 (cardsD1 v3) !inE eqxx ?orbT /=.
case/andP: (dA_diff (dAr (dAsl dAi1j1))) => -> /= _.
set A2 := _ :\  v1; case: (set_0Vmem A2) => [->|[u]].
  by rewrite cards0 addn0.
rewrite 4!inE dirr_constt_oppr pAi2j2E !inE V5eV3.
case/and3P=> HH; case: (boolP (ndirr _ == ndirr _))=> [/eqP|_].
  by move/ndirr_inj=> HH1; case/eqP: HH.
rewrite {HH}(negPf HH) !orbF /= => /orP [] /eqP->.
  rewrite (negPf (ndirr_diff _)) eq_sym.
  by case/andP: (dA_diff (dAr (dAsl dAi1j1))) => _ /negPf->.
rewrite (negPf (ndirr_diff _)) eq_sym.
by case/andP: (dA_diff (dAr (dAr dAi1j1))) => _ /negPf->.
Qed.

Fact dAr_n_notin i j k v1 v2 v3 : j != 0 -> 
  dA i k v1 v2 v3 -> ndirr v1 \notin pA i j.
Proof.
move=> NZj dAikE.
case: (boolP (k == j))=> [/eqP<- | JdK].
  by apply: dirr_constt_oppl; apply: dA_in dAikE.
case/and3P: dAikE=> NZi NZk pAikE; apply/negP=> V1iP.
case: (beta_diff NZi NZk NZi NZj)=> _ _ _ _ /(_ JdK) [_].
rewrite (cardsD1 v1) (eqP pAikE) inE dirr_constt_oppr V1iP.
by rewrite !inE eqxx.
Qed.

Fact dAl_n_notin i j k v1 v2 v3 : j != 0 ->
  dA k i v1 v2 v3 -> ndirr v1 \notin pA j i.
Proof.
move=> NZj dAikE.
case: (boolP (k == j))=> [/eqP<- | JdK].
  by apply: dirr_constt_oppl; apply: dA_in dAikE.
case/and3P: dAikE=> NZk NZi pAikE; apply/negP=> V1iP.
case: (beta_diff NZk NZi NZj NZi)=> _ _ _ /(_ JdK) [_].
rewrite (cardsD1 v1) (eqP pAikE) inE dirr_constt_oppr V1iP.
by rewrite !inE eqxx.
Qed.

Fact dAr_n_notins i j k v1 v2 v3 : j != 0 -> dA i k v1 v2 v3 ->
 [&& ndirr v1 \notin pA i j, ndirr v2 \notin pA i j & ndirr v3 \notin pA i j].
Proof.
move=> NZj HB.
by rewrite !(dAr_n_notin _ HB, dAr_n_notin _ (dAsl HB), dAr_n_notin _ (dAr HB)).
Qed.

Fact dAl_n_notins i j k v1 v2 v3 :  j != 0 -> dA k i v1 v2 v3 ->
 [&& ndirr v1 \notin pA j i, ndirr v2 \notin pA j i & ndirr v3 \notin pA j i].
Proof.
move=> NZj HB.
by rewrite !(dAl_n_notin _ HB, dAl_n_notin _ (dAsl HB), dAl_n_notin _ (dAr HB)).
Qed.

(* Technical lemma *)
Let main_aux i1 i2 i3 i4 j j' x1 x2 x3 x4 x5 x6 x7 :
    i1 != 0 -> j' != 0 -> j' != j ->
    i4 != i3 -> i4 != i2 -> i4 != i1 -> i3 != i2 -> i3 != i1 -> i2 != i1 -> 
    dA i1 j x1 x2 x3 -> dA i2 j x1 x4 x5 ->
    dA i3 j x2 x4 x6 -> dA i4 j x1 x6 x7 ->
  x1 \in pA i1 j' -> dA i1 j' x1 (ndirr x5) (ndirr x7).
Proof.
move=> NZi1 NZj' J'dJ I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1 Ai1j Ai2j Ai3j Ai4j.
case/(dAEI NZi1 NZj')=> [[x x'] /= Ai1j'].
have JdJ' : j != j' by rewrite eq_sym.
wlog: x x' x1 x4 x5  Ai1j Ai2j Ai3j Ai4j Ai1j' 
  / x == ndirr x4 \/ x == ndirr x5 => [WL|].
  case/or4P: (dA2_split I2dI1 JdJ' Ai2j Ai1j')=> /andP [] x'E d'E.
  - by apply: WL Ai1j Ai2j Ai3j Ai4j Ai1j' _; left.
  - by apply: WL Ai1j Ai2j Ai3j Ai4j Ai1j' _; right.
  - by apply: WL Ai1j Ai2j Ai3j Ai4j (dAsr Ai1j') _; left.
  by apply: WL Ai1j Ai2j Ai3j Ai4j (dAsr Ai1j') _; right.
case=> xE; rewrite {x xE}(eqP xE) in Ai1j'.
  case/or4P: (dA2_n_split I3dI1 JdJ' (dAsl Ai3j) (dAsl Ai1j'))
          => /andP [] xE dE.
  - by case/and3P: (dA_diffs Ai1j); rewrite (eqP xE) eqxx.
  - by case/and3P: (dA_diffs Ai4j); rewrite (eqP xE) eqxx.
  - rewrite (eqP xE) in Ai1j'.
    by case/and4P: (dA2r_diffs  JdJ' Ai1j Ai1j'); rewrite eqxx.
  rewrite (eqP xE) in Ai1j'.
  case/or4P: (dA2_split I4dI1 JdJ' Ai4j Ai1j')=> /andP [] x''E d''E.
  - case/and3P: (dA_diffs (dAr Ai1j')); move/eqP: x''E => /ndirr_inj ->.
    by rewrite ndirrK eqxx andbF.
  - by case/andP: d''E; rewrite eqxx.
  - by case/negP: (ndirr_diff x6); rewrite eq_sym.
  by case/and3P: (dA_diffs Ai4j); rewrite (eqP x''E) eqxx andbF.
case/or4P: (dA2_split I4dI1 JdJ' Ai4j Ai1j')=> /andP [] xE dE.
- case/and4P: (dA2l_diffs  I3dI2 (dAsl Ai3j) (dAsl Ai2j)).
  by move/eqP: xE => /ndirr_inj ->; rewrite eqxx.
- case/and4P: (dA2l_diffs  I4dI2 Ai4j Ai2j).
  by move/eqP: xE => /ndirr_inj ->; rewrite eqxx.
- rewrite (eqP xE) in Ai1j'.
  case/or4P: (dA2_n_split I3dI1 JdJ' (dAr Ai3j) (dAr Ai1j'))
        => /andP [] x'E d'E.
  - by case/and3P: (dA_diffs Ai1j); rewrite (eqP x'E) eqxx.
  - by case/and3P: (dA_diffs Ai2j); rewrite (eqP x'E) eqxx.
  - case/and3P: (dAl_n_notins NZi1 Ai2j).
    by rewrite (eqP x'E) (dA_in (dAsl Ai1j)).
  by case/and3P: (dA_diffs Ai2j); rewrite -(eqP x'E) eqxx andbF.
by rewrite (eqP xE) in Ai1j'.
Qed.

(* This is almost PeterFalvi (3.5.4). *)
Fact cfCycTIiso_basis_line j : 
  {xi | if j == 0 then xi = dirr1 G else forall i, i != 0 -> xi \in pA i j}.
Proof.
have [_ | NZj] := altP eqP; first by exists (dirr1 G).
pose i1 : Iirr W'1 := inZp 1.
pose i2 : Iirr W'1 := inZp 2.
have NZi1 : i1 != 0.
  apply/eqP; move/val_eqP=> /=.
  by rewrite modn_small // (leq_trans _ H2Lw'1).
have NZi2 : i2 != 0.
  apply/eqP; move/val_eqP=> /=.
  by rewrite modn_small //.
have I2dI1 : i2 != i1.
  apply/eqP; move/val_eqP=> /=.
  by rewrite !modn_small // (leq_trans _ H2Lw'1).
move: H2Lw'1; rewrite leq_eqVlt; case: (boolP (_ == _))=> [/eqP H3Em _ | _ /=].
  have F P : P i1 -> P i2 -> forall i, i != 0 -> P i.
    move=> HP1 HP2 i NZi.
    have: (i < 3)%N by rewrite -(modZp i) -{2}H3Em /= ltn_mod.
    rewrite ltnS leq_eqVlt; case: (boolP (_ == _))=> [/eqP HH _| _ /=].
      suff->: i = i2 by done.
      by apply/val_eqP=> /=; rewrite -{2}H3Em HH.
    rewrite ltnS leq_eqVlt; case: (boolP (_ == _))=> [/eqP HH _| _ /=].
      suff->: i = i1 by done.
      by apply/val_eqP=> /=; rewrite -{2}H3Em HH.
    rewrite ltnS leq_eqVlt; case: (boolP (_ == _))=> [/eqP HH _| _ /=].
      case/eqP: NZi; suff->: i = 0 by done.
      by apply/val_eqP; rewrite /= HH.
    by rewrite ltn0.
  case: (dAE NZi1 NZj)=> [[[v1 v2] v3] /=  Ai1j].
  move: (dAl_split NZi2 Ai1j).
  case: (boolP (_ \in _))=> [HH _ | _].
    by exists v1; apply: F (dA_in Ai1j) _.
  case: (boolP (_ \in _))=> [HH _ | _ /= HH].
    by exists v2; apply: F (dA_in (dAsl Ai1j)) _.
  by exists v3; apply: F (dA_in (dAr Ai1j)) _.
rewrite leq_eqVlt; case: (boolP (_ == _))=> [/eqP HH|_ /= H4Lm].
  by move: Oddw'1; rewrite -{1}HH.
case: (dAE NZi1 NZj)=> [] [[x1 x2] x3 /= Ai1j].
wlog:  x1 x2 x3 Ai1j / x1 \in pA i2 j => [WL | X1iAi2].
  move: (dAl_split NZi2 Ai1j).
  case: (boolP (_ \in _))=> [X1iAi2 _ | _]; first by apply: WL Ai1j X1iAi2.
  case: (boolP (_ \in _))=> [X2iAi2 _ | /= _ X3iAi2].
    by apply: WL (dAsl Ai1j) X2iAi2.
  by apply: WL (dAr Ai1j) X3iAi2.
case: (dAEI NZi2 NZj X1iAi2)=> {X1iAi2}[] [x4 x5] /= Ai2j.
case: (boolP [forall (i : 'I__| i != 0), x1 \in pA i j]) => [/forall_inP HH|].
  by exists x1 => // i /HH.
rewrite negb_forall; move/existsP=> HH; suff: false by [].
case: HH=> i3; rewrite negb_imply; case/andP=> NZi3 X3niAi3.
have I3dI1: i3 != i1.
  by apply: contra X3niAi3; move/eqP->; move: (dA_in Ai1j).
have I3dI2: i3 != i2.
  by apply: contra X3niAi3; move/eqP->; move: (dA_in Ai2j).
wlog:  x2 x3 Ai1j / x2 \in pA i3 j => [WL | X2iAi3].
  case/or3P: (dAl_split NZi3 Ai1j)=> XiAi3; first by case/negP: X3niAi3.
    by apply: WL Ai1j XiAi3.
  by apply: WL (dAsr Ai1j) XiAi3.
case: (dAEI NZi3 NZj X2iAi3)=> {X2iAi3}[] [x' x6] /= Ai3j.
wlog: x' x4 x5 x6 Ai2j Ai3j / (x4 == x')=> WL.
  case/or3P: (dAl_split NZi3 Ai2j)=> X4iAi3; first by case/negP: X3niAi3.
    case/or3P: (dA_in_split Ai3j X4iAi3)=> x4E.
    - by case/and4P: (dA2l_diffs  I2dI1 Ai2j Ai1j); rewrite (eqP x4E) eqxx.
    - by apply: WL Ai2j Ai3j x4E.
    by apply: WL Ai2j (dAsr Ai3j) x4E.
  case/or3P: (dA_in_split Ai3j X4iAi3)=> x5E.
  - case/and4P: (dA2l_diffs  I2dI1 (dAsr Ai2j) Ai1j).
    by rewrite (eqP x5E) eqxx=> /negP [].
  - by apply: WL (dAsr Ai2j) Ai3j x5E.
  by apply: WL (dAsr Ai2j) (dAsr Ai3j) x5E.
rewrite -(eqP WL) {x' WL} in Ai3j.
move: H4Lm; rewrite -[Nirr _]card_ord.
rewrite (cardD1 (0: 'I__)) (cardD1 i1) (cardD1 i2) (cardD1 i3) !inE ?eqxx.
rewrite NZi1 NZi2 I2dI1 NZi3 I3dI1 I3dI2 !add1n !ltnS.
case/card_gt0P=> i4; rewrite !inE=> /and5P [] I4dI3 I4dI2 I4dI1 NZi4 _.
case: (dAE NZi4 NZj)=> [] [[x x'] x7] /= Ai4j.
wlog: x x' x1 x2 x3 x4 x5 x6 x7 i1 i2 i3 i4
      NZi1 NZi2 NZi3 {X3niAi3}NZi4 I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1 
      Ai1j Ai2j Ai3j Ai4j /
   ((x1 == x /\ x6 == x') \/ 
    [/\ x == x3, x' == x5 & x7 == x6])=> [WL |].
 case: (boolP (x3 \in pA i4 j))=> [X3iAi4 | X3niAi4].
    wlog: x x' x7 Ai4j / x = x3 => [WL1|x3E].
      case/or3P: (dA_in_split Ai4j X3iAi4)=> 
          /eqP x3E; first by apply: WL1 Ai4j _.
        by apply: WL1 (dAsl Ai4j) _.
      by apply: WL1 (dAr Ai4j) _.
    have X1niAi4: x1 \notin pA i4 j.
      apply/negP=> X1iAi4; rewrite x3E in Ai4j.
      case/or3P: (dA_in_split Ai4j X1iAi4)=> x4E.
      - by case/and3P: (dA_diffs Ai1j)=> _ _ /andP [] /negP.
      - case/and4P: (dA2l_diffs  I4dI1 Ai4j (dAr Ai1j)).
        by rewrite (eqP x4E) eqxx.
      case/and4P: (dA2l_diffs  I4dI1 Ai4j (dAr Ai1j)).
      by rewrite (eqP x4E) eqxx.
    case: (boolP (x4 \in pA i4 j))=> [X4iAi4 | X4niAi4].
      wlog: x' x7 Ai4j / x' = x4 => [WL1 | x'E].
        case/or3P: (dA_in_split Ai4j X4iAi4)=> /eqP x4E.
        - case/and4P: (dA2l_diffs  I2dI1 Ai2j Ai1j)=> //.
          by rewrite -x3E x4E eqxx.
        - by apply: WL1 Ai4j _.
        by apply: WL1 (dAsr Ai4j) _.
      move: {Ai1j}(dAsl Ai1j)=> Ai1j.
      move: {Ai3j}(dAsl Ai3j)=> Ai3j.
      move: {Ai4j}(dAsl Ai4j)=> Ai4j.
      have x4Ni1: x4 \notin pA i1 j.
        have Di1i2 : i1 != i2 by rewrite eq_sym.
        case/and4P: (dA2l_diffs  I2dI1 Ai2j (dAsl Ai1j))=> 
           /andP [] Hv1 _ /andP [] Hv2 _ _ _.
        apply/negP=> X4iAi1.
        case/or3P: (dA_in_split (dAsl Ai1j) X4iAi1)=> x4E; 
            [| case/negP: Hv1 | case/negP: Hv2]=> //.
        case/and3P: (dA_diffs Ai1j)=> /andP [] /negP []; rewrite eq_sym. 
        by case/negP: X1niAi4; rewrite -(eqP x4E).
      apply: WL Ai3j (dAsl Ai2j) Ai1j Ai4j _; rewrite // eq_sym //.
      by left; split; apply /eqP.
    wlog: x' x7 Ai4j / x' = x5=> [WL1|].
      case/or3P: (dAl_split NZi4 Ai2j)=> XiAi4; first by case/negP: X1niAi4.
        by case/negP: X4niAi4.
      case/or3P: (dA_in_split Ai4j XiAi4)=> /eqP xE.
      - have I1dI2 : i1 != i2 by rewrite eq_sym.
        case/and4P: (dA2l_diffs  I1dI2 Ai1j Ai2j)=> _ _ _.
        by rewrite xE -x3E eqxx.
      - by apply: WL1 Ai4j _.
      by apply: WL1 (dAsr Ai4j) _.
    move=> x'E.
    apply: WL (Ai1j) (Ai2j) (Ai3j) (Ai4j) _ => //; 
       right; split; apply/eqP => //.
    rewrite x3E x'E in Ai4j.  
    case/or3P: (dAl_split NZi4 Ai3j)=> XiAi4.
    - case/and4P: (dA2l_diffs  I4dI1 Ai4j (dAr Ai1j)).
      by case/or3P: (dA_in_split Ai4j XiAi4)=> /eqP xE;
         first case/and3P: (dA_diffs (dAr Ai1j))=> _ _ /andP [];
         rewrite xE eqxx.
    - by case/negP: X4niAi4.
    case/or3P: (dA_in_split Ai4j XiAi4)=> /eqP xE //.
      case/and4P: (dA2l_diffs  I3dI1 Ai3j (dAsl Ai1j)) => _ _ _.
      by rewrite xE -x3E eqxx.
    case/and4P: (dA2l_diffs  I3dI2 (dAsl Ai3j) (dAsl Ai2j))=> _ _ _.
    by rewrite xE eqxx.
  wlog: x x' x7 x1 x2 x3 x4 x5 x6 i1 i2 i3 
        NZi1 NZi2 NZi3 I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1
       {X3niAi4 X3niAi3}Ai1j Ai2j Ai3j Ai4j
       / x == x1 => [WL1|].
    case/or3P: (dAl_split NZi4 Ai1j)=> XiAi4; last by case/negP: X3niAi4.
      case/or3P: (dA_in_split Ai4j XiAi4)=> /eqP xE //.
      - by apply: WL1 Ai1j Ai2j Ai3j Ai4j _ => //; rewrite xE eqxx.
      - by apply: WL1 Ai1j Ai2j Ai3j (dAsl Ai4j) _ 
               => //; rewrite xE eqxx.
      by apply: WL1 Ai1j Ai2j Ai3j (dAr Ai4j) _ 
               => //; rewrite xE eqxx.
    case/or3P: (dA_in_split Ai4j XiAi4)=> /eqP xE //.
    - by apply: WL1 (dAsl Ai1j) Ai3j Ai2j Ai4j _; 
         rewrite // eq_sym // xE.
    - by apply: WL1 (dAsl Ai1j) Ai3j Ai2j (dAsl Ai4j) _; 
         rewrite // eq_sym // xE.
    by apply: WL1 (dAsl Ai1j) Ai3j Ai2j (dAr Ai4j) _; 
         rewrite // eq_sym // xE.
  move/eqP=> xE.
  wlog: x' x7 Ai4j / x' == x6 => [WL1 | x'E].
    case/or3P: (dAl_split NZi4 Ai3j)=> XiAi4.
    - rewrite xE in Ai4j; have I1dI4 : i1 != i4 by rewrite eq_sym.
      by case/negP: (dA2l_notin I1dI4 Ai1j Ai4j).
    - rewrite xE in Ai4j; have Di2i4 : i2 != i4 by rewrite eq_sym.
      by case/negP: (dA2l_notin  Di2i4 Ai2j Ai4j).
    case/or3P: (dA_in_split Ai4j XiAi4)=> /eqP x6E //.
    - rewrite x6E xE in Ai3j.
      case/and4P: (dA2l_diffs I3dI1 (dAr Ai3j) Ai1j).
      by rewrite eqxx.
    - by apply: WL1 Ai4j _; rewrite x6E eqxx.
    by apply: WL1 (dAsr Ai4j) _; rewrite x6E eqxx.
  by apply: WL Ai1j Ai2j Ai3j Ai4j _ => //; left; split;
    rewrite ?xE ?(eqP x'E) eqxx.
have [j'[NZj' J'dJ]]: exists j', j' != 0 /\ j'!= j.
  pose j1 : Iirr W'2 := inZp 1.
  pose j2 : Iirr W'2 := inZp 2.
  have NZj1 : j1 != 0.
    apply/eqP; move/val_eqP=> /=.
    by rewrite modn_small // (leq_trans _ H2Lw'2).
  have NZj2 : j2 != 0.
    apply/eqP; move/val_eqP=> /=.
    by rewrite modn_small //.
  have J2dJ1 : j2 != j1.
    apply/eqP; move/val_eqP=> /=.
    by rewrite !modn_small // (leq_trans _ H2Lw'2).
  exists (if j == j1 then j2 else j1).
  by case: (boolP (j == j1))=> [/eqP -> |]; split=> //; rewrite eq_sym. 
case=> [[xE x'E] | [xE x'E x7E]]; last first.
  (* This is step (3.5.4.6). *)
  rewrite (eqP xE) (eqP x'E) {xE x'E x7E}(eqP x7E) in Ai4j.
  wlog: i1 i2 i3 i4 x1 x2 x3 x4 x5 x6
        NZi4 NZi3 NZi2 NZi1 I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1 
        Ai1j Ai2j Ai3j Ai4j / x1 \in pA i1 j' => [WL | X1iAi1].
    case/or3P: (dAr_split NZj' Ai1j)=> XiAi1.
    - by apply: WL Ai1j Ai2j Ai3j Ai4j _.
    - by apply: WL (dAsl Ai1j) Ai3j Ai2j (dAsr Ai4j) _;
         rewrite // eq_sym.
    by apply: WL (dAr Ai1j) Ai4j (dAsr Ai2j) (dAsr Ai3j) _;
       rewrite // eq_sym.
  case: (dAEI NZi1 NZj' X1iAi1)=> {x x' X1iAi1}[] [x x'] /= Ai1j'.
  wlog: i1 i2 i3 i4 x x' x1 x2 x3 x4 x5 x6 
        NZi4 NZi3 NZi2 NZi1 I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1 
        Ai1j Ai2j Ai3j Ai4j Ai1j' / x == ndirr x4 => [WL | x'E].
    have JdJ' : j != j' by rewrite eq_sym.
    case/or4P: (dA2_split I2dI1 JdJ' Ai2j Ai1j')=> /andP [] xE dE. 
    - by apply: WL Ai1j Ai2j Ai3j Ai4j Ai1j' _.
    - by apply: WL (dAsr Ai1j) (dAsr Ai2j) Ai4j Ai3j Ai1j' _;
         rewrite // eq_sym.
    - by apply: WL Ai1j Ai2j Ai3j Ai4j (dAsr Ai1j') _.
    by apply: WL (dAsr Ai1j) (dAsr Ai2j) Ai4j Ai3j 
                 (dAsr Ai1j')_; rewrite // eq_sym.
  rewrite {x'E}(eqP x'E) in Ai1j'.
  move: {Ai1j'}(dAsl Ai1j')=> Ai1j'.
  move: {Ai3j}(dAsl Ai3j)=> Ai3j.
  have JdJ' : j != j' by rewrite eq_sym.
  case/or4P: (dA2_n_split I3dI1 JdJ' Ai3j Ai1j')=> /andP [] xE dE.
  - by case/and3P: (dA_diffs Ai1j); rewrite (eqP xE) eqxx.
  - rewrite (eqP xE) in Ai1j.
    by case/and4P: (dA2l_diffs  I3dI1 (dAr Ai3j) Ai1j); rewrite eqxx.
  - rewrite (eqP xE) in Ai1j'.
    by case/and4P: (dA2r_diffs  JdJ' Ai1j (dAsl Ai1j')); rewrite eqxx.
  rewrite (eqP xE) in Ai1j'.
  move: {Ai1j'}(dAr Ai1j')=> Ai1j'.
  move: {Ai4j}(dAr Ai4j)=> Ai4j.
  case/or4P: (dA2_split I4dI1 JdJ' Ai4j Ai1j')=> /andP [] x'E d'E.
  - case/and4P: (dA2l_diffs  I2dI1 Ai2j Ai1j).
    by move/eqP: x'E => /ndirr_inj->; rewrite eqxx.
  - case/and3P: (dA_diffs Ai2j).
    by move/eqP: x'E => /ndirr_inj->; rewrite eqxx.
  - by case/and3P: (dA_diffs Ai1j); rewrite -(eqP x'E) eqxx andbF.
  by case/and3P: (dA_diffs Ai2j); rewrite -(eqP x'E) eqxx andbF.
rewrite -(eqP xE) -{x x' xE x'E}(eqP x'E) in Ai4j.
 (* This is step (3.5.4.1). *)
have F1: x1 \in pA i1 j' -> dA i1 j' x1 (ndirr x5) (ndirr x7).
  by apply: main_aux Ai1j Ai2j Ai3j Ai4j.
have F2: x1 \in pA i2 j' -> dA i2 j' x1 (ndirr x3) (ndirr x7).
  by rewrite eq_sym in I2dI1; apply: main_aux Ai2j Ai1j (dAsl Ai3j) Ai4j.
have F3: x1 \in pA i4 j' -> dA i4 j' x1 (ndirr x3) (ndirr x5).
  by apply: main_aux Ai4j Ai1j (dAr Ai3j) Ai2j; rewrite // eq_sym.
 (* This is step (3.5.4.2). *)
wlog: i1 i2 i4 x2 x3 x4 x5 x6 x7
      NZi4 NZi2 NZi1 I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1 F1 F2 F3
      Ai1j Ai2j Ai3j Ai4j / x2 \in pA i3 j' => [WL|].
  case/or3P: (dAr_split NZj' Ai3j).
  - by apply: WL Ai1j Ai2j Ai3j Ai4j.
  - apply: WL Ai2j Ai1j (dAsl Ai3j) Ai4j=> //; first by rewrite eq_sym. 
    by move=> // HH; apply: dAsr; apply: F3.
  apply: WL Ai4j Ai2j (dAsr (dAr Ai3j)) Ai1j => //; try by rewrite eq_sym. 
  - by move=> HH; apply: dAsr; apply: F3.
  - by move=> HH; apply: dAsr; apply: F2.
  by move=> HH; apply: dAsr; apply: F1.
case/(dAEI NZi3 NZj')=> [] [x x8] /= Ai3j'.
move: {Ai1j} (dAsl Ai1j)=> Ai1j.
wlog: x x8 x1 x2 x3 F1 F2 F3 Ai1j Ai2j Ai3j Ai4j Ai3j' 
          / x == ndirr x1 \/ x == ndirr x3 => [WL|].
  case/or4P: (dA2_split I3dI1 J'dJ Ai3j' Ai1j)=> /andP [] x'E d'E.
  - apply: WL Ai1j Ai2j Ai3j Ai4j Ai3j' _=> //.
    by rewrite (eqP x'E) ndirrK eqxx; left.
  - apply: WL Ai1j Ai2j Ai3j Ai4j (dAsr Ai3j') _=> //. 
    by rewrite (eqP x'E) ndirrK eqxx; left.
  - apply: WL Ai1j Ai2j Ai3j Ai4j Ai3j' _ => //.
    by rewrite (eqP x'E) ndirrK eqxx; right.
  apply: WL Ai1j Ai2j Ai3j Ai4j (dAsr Ai3j')  _ => //.
  by rewrite // (eqP x'E) ndirrK eqxx; right.
move: {Ai1j} (dAsl Ai1j)=> Ai1j.
case=> /eqP HH; rewrite {x}HH in Ai3j'.
  move: {Ai3j'} (dAsl Ai3j')=> Ai3j'.
  have Di2i3 : i2 != i3 by rewrite eq_sym.
  have JdJ' : j != j' by rewrite eq_sym.
  case/or4P: (dA2_n_split Di2i3 JdJ' Ai2j Ai3j')=> 
    /andP [] x'E d'E.
  - by case/and3P: (dA_diffs Ai3j); rewrite (eqP x'E) eqxx.
  - case/and4P: (dA2l_diffs  I3dI2 (dAsl Ai3j) (dAsl Ai2j)).
    by rewrite (eqP x'E) eqxx.
  - rewrite (eqP x'E) in Ai3j'.
    case/or4P: (dA2_n_split I4dI3 JdJ' Ai4j Ai3j')=> /andP [] x''E d''E.
    - by case/and3P: (dA_diffs Ai3j); rewrite (eqP x''E) eqxx.
    - by case/and4P: (dA2l_diffs  I4dI1 Ai4j Ai1j); rewrite (eqP x''E) eqxx.
    - by case/and3P: (dA_diffs Ai3j); rewrite (eqP x''E) eqxx.
    by case/and4P: (dA2l_diffs  I4dI2 Ai4j Ai2j); rewrite (eqP x''E) eqxx.
  rewrite (eqP x'E) in Ai3j'.
  case/or4P: (dA2_n_split I4dI3 JdJ' Ai4j Ai3j')=> /andP [] x''E d''E.
  - by case/and3P: (dA_diffs Ai3j); rewrite (eqP x''E) eq_refl.
  - by case/and4P: (dA2l_diffs  I4dI1 Ai4j Ai1j); rewrite (eqP x''E) eqxx.
  - by case/and4P: (dA2l_diffs  I4dI2 Ai4j Ai2j); rewrite (eqP x''E) eqxx.
  by case/and4P: (dA2l_diffs  I4dI2 Ai4j Ai2j); rewrite (eqP x''E) eqxx.
 (* This is step (3.5.4.3). *)
case/or3P: (dAr_split NZj' Ai1j); first 2 last.
- case/(dAEI NZi1 NZj')=> [] [x x'] /= Ai1j'.
  by case/and3P: (dAl_n_notins NZi1 Ai3j'); rewrite ndirrK (dA_in Ai1j').
- move/F1=> Ai1j'.
  case/or3P: (dAl_split NZi3 Ai1j').
  - move/(dA_in_split Ai3j')=> /or3P [] xE.
    - by case/and3P: (dA_diffs Ai1j); rewrite (eqP xE) eqxx.
    - by case/and3P: (dA_diffs Ai1j); rewrite (eqP xE) eqxx andbF.
   rewrite -(eqP xE) in Ai3j'.
   case/or4P: (dA2_split I3dI1 J'dJ (dAr Ai3j') Ai1j)=> /andP [] x'E d'E.
   - by case/andP: d'E; rewrite ndirrK eqxx.
   - by case/andP: d'E; rewrite (eqP x'E) ndirrK eqxx.
   - by case/andP: d'E; rewrite (eqP x'E) ndirrK eqxx.
   by case/andP: d'E; rewrite eqxx.
  - move/(dA_in_split Ai3j')=> /or3P [] xE.
    - rewrite -(eqP xE) in Ai3j; move: (dAl_n_notins NZi3 (dAsl Ai2j)).
      by rewrite (dA_in Ai3j) !andbF.
    - case/and4P: (dA2l_diffs  I2dI1 Ai2j Ai1j).
      by move/eqP: xE => /ndirr_inj ->; rewrite eqxx.
    rewrite -(eqP xE) in Ai3j'.
    have JdJ' : j != j' by rewrite eq_sym.
    have Di2i3 : i2 != i3 by rewrite eq_sym.
    case/or4P: (dA2_n_split Di2i3 JdJ' (dAr Ai2j) (dAr Ai3j'))
          => /andP [] x'E d'E.
    - by case/and3P: (dA_diffs Ai1j); rewrite (eqP x'E) eqxx.
    - by case/and3P: (dA_diffs Ai3j); rewrite (eqP x'E) eqxx.
    - by case/and3P: (dA_diffs Ai1j); rewrite -(eqP x'E) eqxx andbF.
    move: (dAl_n_notins NZi2 Ai1j).
    by rewrite (eqP x'E) (dA_in (dAsl Ai2j)) !andbF.
  move/(dA_in_split Ai3j')=> /or3P [] xE.
  - rewrite -(eqP xE) in Ai3j; case/and3P: (dAl_n_notins NZi4 (dAr Ai3j)).
    by rewrite ndirrK (dA_in (dAr Ai4j)).
  - case/and4P: (dA2l_diffs  I4dI1 Ai4j Ai1j).
    by move/eqP: xE => /ndirr_inj ->; rewrite eqxx.
  rewrite -(eqP xE) in Ai3j'; have JdJ' : j != j' by rewrite eq_sym.
  case/or4P: (dA2_n_split I4dI3 JdJ' (dAr Ai4j) (dAr Ai3j'))
       => /andP [] x'E d'E.
  - by case/and3P: (dA_diffs Ai1j); rewrite (eqP x'E) eqxx.
  - by case/and3P: (dA_diffs Ai3j); rewrite (eqP x'E) eqxx.
  - by case/and3P: (dA_diffs Ai1j); rewrite -(eqP x'E) eqxx andbF.
  rewrite -(eqP x'E) in Ai3j.
  case/and3P: (dAl_n_notins NZi3 (dAsl Ai1j)).
  by rewrite (dA_in (dAr Ai3j)).
case/(dAEI NZi1 NZj')=> [] [x x'] /= Ai1j'.
wlog: x x' x1 x2 x3 x4 x5 x6 x7 x8 i1 i2 i3 i4
      NZi1 NZi2 NZi3 NZi4 I4dI3 I4dI2 I4dI1 I3dI2 I3dI1 I2dI1  
      F1 F2 F3      
      Ai1j Ai2j Ai3j Ai4j Ai1j' Ai3j' / x == ndirr x4 => [WL | xE].
  have JdJ' : j != j' by rewrite eq_sym.
  case/or4P: (dA2_split I3dI1 JdJ' Ai3j Ai1j')=> /andP [] xE dE.
  - by apply: WL Ai1j Ai2j Ai3j Ai4j Ai1j' Ai3j' xE.
  - apply: WL Ai1j Ai4j (dAsr Ai3j) Ai2j Ai1j' Ai3j' xE => //;
         try by rewrite eq_sym.
    by move=> HH; apply: dAsr; apply: F1.
  - by apply: WL Ai1j Ai2j Ai3j Ai4j (dAsr Ai1j') Ai3j' xE => //;
       rewrite eq_sym.
  apply: WL Ai1j Ai4j (dAsr Ai3j) Ai2j (dAsr Ai1j') Ai3j' xE=> //;
       try by rewrite eq_sym.
  by move=> HH; apply: dAsr; apply: F1.
rewrite {x xE}(eqP xE) in Ai1j'.
move: {Ai1j'} (dAsl Ai1j')=> Ai1j'.
move: {Ai2j} (dAsl Ai2j)=> Ai2j.
have JdJ' : j != j' by rewrite eq_sym.
case/or4P: (dA2_n_split I2dI1 JdJ' Ai2j Ai1j')=> /andP [] x'E d'E.
- by case/and3P: (dA_diffs Ai1j); rewrite (eqP x'E) eqxx.
- case/and4P: (dA2l_diffs  I3dI2 (dAsl Ai3j) Ai2j).
  by rewrite (eqP x'E) eqxx.
- rewrite (eqP x'E) in Ai1j'.
  case/and4P: (dA2r_diffs  J'dJ (dAr Ai1j') Ai1j).
  by rewrite eqxx.
rewrite {x' x'E d'E}(eqP x'E) in Ai1j'.
move: {Ai1j'} (dAsl Ai1j')=> Ai1j'.
move: {Ai2j} (dAsl Ai2j)=> Ai2j.
 (* This is step (3.5.4.4). *)
case/or3P: (dAr_split NZj' Ai2j).
- move/F2=> Ai2j'.
  case/or3P: (dAl_split NZi1 Ai2j'); move/(dA_in_split Ai1j'); 
         case/or3P=> /eqP xE //.
  - by case/and3P: (dA_diffs Ai1j); rewrite xE eqxx.
  - by case/and3P: (dA_diffs Ai2j); rewrite -xE eqxx andbF.
  - by case/and3P: (dA_diffs Ai2j); rewrite  xE eqxx.
  - by case/and3P: (dA_diffs Ai1j); rewrite -xE eqxx andbF.
  - case/and4P: (dA2l_diffs  I3dI1 Ai3j' Ai1j').
    by rewrite xE eqxx.
  - case/and4P: (dA2l_diffs  I3dI1 Ai3j' Ai1j').
    by rewrite xE eqxx.
  - case/and4P: (dA2l_diffs  I3dI2 (dAsl Ai3j') (dAsl Ai2j')).
    by rewrite -xE eqxx.
  - case/and4P: (dA2r_diffs  J'dJ Ai2j' Ai2j)=> _ _.
    by rewrite xE eqxx andbF.
  case/and4P: (dA2r_diffs  J'dJ Ai2j' Ai2j)=> _ _.
  by rewrite xE eqxx.
- move=> X4iAi2; case/and3P: (dAl_n_notins NZi2 Ai1j').
  by rewrite ndirrK => _ /negP [].
case/(dAEI NZi2 NZj')=> [[x x9] /= Ai2j'].
wlog: x x9 Ai2j' / x = x8 => [WL | xE].
  case/or3P: (dAl_split NZi2 Ai3j').
  - move=> x2Ii2; move: {Ai1j'}(dAr Ai1j') => Ai1j'.
    case/or3P: (dA_in_split Ai2j' x2Ii2)=> x2E.
    - by case/and3P: (dA_diffs Ai1j'); rewrite (eqP x2E) eqxx.  
    - case/and4P: (dA2l_diffs  I2dI1 Ai2j' Ai1j').
      by rewrite (eqP x2E) eqxx.
    case/and4P: (dA2l_diffs  I2dI1 Ai2j' Ai1j').
    by rewrite (eqP x2E) eqxx.
  - move=> X3iAi2.
    case/or3P: (dA_in_split Ai2j' X3iAi2)=> x3E.
    - case/and4P: (dA2l_diffs  I3dI1 Ai3j' Ai1j').
      by rewrite (eqP x3E) eqxx.
    - rewrite -(eqP x3E) in Ai2j'.
      have I1dI2 : i1 != i2 by rewrite eq_sym.
      case/or4P: (dA2_n_split I1dI2 JdJ' (dAr Ai1j) (dAsl Ai2j'))
           => /andP [] xE dE.
      - by case/and3P: (dA_diffs Ai2j); rewrite (eqP xE) eqxx.
      - by case/and3P: (dA_diffs Ai1j'); rewrite (eqP xE) eqxx.
      - case/and4P: (dA2r_diffs  J'dJ Ai2j' (dAr Ai2j)).
        by rewrite (eqP xE) eqxx.
      case/and4P: (dA2l_diffs  I2dI1 Ai2j' (dAr Ai1j')).
      by rewrite (eqP xE) eqxx.
    rewrite -(eqP x3E) in Ai2j'.
    have I1dI2 : i1 != i2 by rewrite eq_sym.
    case/or4P: (dA2_n_split I1dI2 JdJ' (dAr Ai1j) (dAr Ai2j'))
        => /andP [] xE dE.
    - by case/and3P: (dA_diffs Ai2j); rewrite (eqP xE) eqxx.
    - by case/and3P: (dA_diffs Ai1j'); rewrite (eqP xE) eqxx.
    - rewrite (eqP xE) in Ai2j'.
      by case/and4P: (dA2r_diffs  J'dJ (dAsl Ai2j') Ai2j); rewrite  eqxx.
    rewrite (eqP xE) in Ai2j'.
    by case/and4P: (dA2l_diffs  I2dI1 (dAsl Ai2j') Ai1j'); rewrite eqxx.
   move/(dA_in_split Ai2j')=> /or3P [] x3E.
   - case/and4P: (dA2l_diffs  I3dI1 Ai3j' Ai1j').
     by rewrite (eqP x3E) eqxx.
   - by apply: WL Ai2j' _; rewrite (eqP x3E).
   by apply: WL (dAsr Ai2j') _; rewrite (eqP x3E).
rewrite {x}xE in Ai2j'.
 (* This is step (3.5.4.5). *)
pose II x := x \in pA i4 j'.
have X1niAj4 : ~~ II x1.
  apply/negP=> /F3 Ai4j'.
  case/and3P: (dAl_n_notins NZi4 Ai1j').
  by rewrite(dA_in (dAr Ai4j')).
have mX1niAj4 : ~~ II (ndirr x1).
 by case/and3P: (dAr_n_notins NZj' Ai4j).
have [NIx2 NIx3] : ~II x2 /\ ~II (ndirr x3).
  have NII: ~ (II x2 /\ II (ndirr x3)).
    case; case/(dAEI NZi4 NZj')=> [[x x'] /= Ai4j' X3iAi4].
     wlog: x x' Ai4j' / x = ndirr x3=> [WL|HH]; last rewrite {}HH in Ai4j'.
       case/or3P: (dA_in_split Ai4j' X3iAi4)=> xE.
       - case/and3P: (dA_diffs Ai1j).
         by rewrite -(eqP xE) eqxx andbF.
       - by apply: WL Ai4j' _; rewrite (eqP xE).
       by apply: WL (dAsr Ai4j') _; rewrite (eqP xE).
     case/and4P: (dA2l_diffs  I4dI3 Ai4j' Ai3j').
     by rewrite eqxx.
  split.
    case/(dAEI NZi4 NZj')=> [[x x'] /= Ai4j'].
    case/or4P: (dA2_split I4dI1 J'dJ Ai4j' (dAsl Ai1j))=> /andP [] xE dE.
    - case/and3P: (dAr_n_notins NZj' Ai4j); rewrite (eqP xE) ndirrK.
      by rewrite (dA_in (dAsl Ai4j')).
    - case/and3P: (dAr_n_notins NZj' Ai4j); rewrite (eqP xE) ndirrK.
      by rewrite (dA_in (dAr Ai4j')).
    - case: NII; rewrite /II (dA_in Ai4j') (eqP xE) ndirrK.
      by rewrite (dA_in (dAsl Ai4j')).
    case: NII; rewrite /II (dA_in Ai4j') (eqP xE) ndirrK.
    by rewrite (dA_in (dAr Ai4j')).
  case/(dAEI NZi4 NZj')=> [[x x'] /= Ai4j'].
  have I1dI4 : i1 != i4 by rewrite eq_sym.
  case/or4P: (dA2_n_split I1dI4 JdJ' (dAr Ai1j) Ai4j')=> /andP [] xE dE.
  - by case/negP: X1niAj4; rewrite -(eqP xE); apply: dA_in (dAsl Ai4j').
  - case: NII; rewrite /II (dA_in Ai4j') -(eqP xE).
    by rewrite (dA_in (dAsl Ai4j')).
  - by case/negP: X1niAj4; rewrite -(eqP xE); apply: dA_in (dAr Ai4j').
  case: NII; rewrite /II (dA_in Ai4j') -(eqP xE).
  by rewrite (dA_in (dAr Ai4j')).
case/or3P: (dAl_split NZi4 Ai3j')=> //.
case/(dAEI NZi4 NZj')=> [[x x'] /= Ai4j'].
have NIx5: ~ II x5.
  move=> x5Ii4; wlog: x x' Ai4j' / x == x5=> [WL| /eqP HH].
    case/or3P: (dA_in_split Ai4j' x5Ii4)=> xE.
    - by case/and3P: (dA_diffs (dAsl Ai2j')); rewrite (eqP xE) eqxx.
    - by apply: WL Ai4j' _; rewrite (eqP xE).
    by apply: WL (dAsr Ai4j') _; rewrite (eqP xE).
  rewrite {}HH in Ai4j'.
  by case/and4P: (dA2l_diffs  I4dI2 (dAsl Ai4j') Ai2j'); rewrite eqxx.
wlog: x x' Ai4j' / x == ndirr x4 => [WL|HH].
  case/or3P: (dAl_split NZi4 Ai1j')=> //.
  move/(dA_in_split Ai4j')=> /or3P [] xE.
  - rewrite -(eqP xE) in Ai3j'.
    case/and4P: (dA2r_diffs  J'dJ Ai3j' Ai3j).
    by rewrite eqxx andbF.
  - by apply: WL Ai4j' _; rewrite (eqP xE).
  by apply: WL (dAsr Ai4j') _; rewrite (eqP xE).
rewrite {HH}(eqP HH) in Ai4j'.
have I2dI4 : i2 != i4 by rewrite eq_sym.
case/or4P: (dA2_n_split I2dI4 JdJ' (dAsl Ai2j) (dAsl Ai4j'))
       => /andP [] xE dE.
- by case/negP: X1niAj4; rewrite -(eqP xE) /II (dA_in Ai4j').
- by case: NIx5; rewrite -(eqP xE) /II (dA_in Ai4j').
- by case/negP: X1niAj4; rewrite -(eqP xE) /II (dA_in (dAr Ai4j')).
by case: NIx5; rewrite -(eqP xE) /II (dA_in (dAr Ai4j')).
Qed.

(* This is the common component of a column; we do not state its uniqueness   *)
(* formally, as it is a direct consequence of (3.5.2).                        *)
Definition ccTIirr (i : Iirr W'2) := sval (cfCycTIiso_basis_line i).

Local Notation gamma_ := ccTIirr.

Fact ccTIirrE i j : i != 0 -> j != 0 -> gamma_ j \in pA i j.
Proof.
move=> NZi NZj; rewrite /gamma_; case: (cfCycTIiso_basis_line j) => x /=.
by rewrite (negPf NZj) => ->.
Qed.

Fact ccTIirr_inN i j j' : 
  i != 0 -> j != 0 -> j' != 0 -> j != j' -> ndirr (gamma_ j') \notin pA i j.
Proof.
move=> NZi NZj NZj' JdJ'; apply/negP=> INg.
case: (dAEI NZi NZj' (ccTIirrE NZi NZj'))=> [[v1 v2 /=] Hv].
by case/andP: (dAr_n_notins NZj Hv)=> /negP.
Qed.

Fact ccTIirr_inP i j j' : (4 < Nirr W'1)%N ->
  i != 0 -> j != 0 -> j' != 0 -> j != j' -> gamma_ j' \notin pA i j.
Proof.
move=> H4Lm NZi NZj NZj' JdJ'; apply/negP=> INg.
case: (dAEI NZi NZj INg)=> [[v1 v2 /=] Aij].
have [i1 [NZi1 IdI1 [i2 [NZi2 IdI2 I1dI2 [i3 [NZi3 IdI3 I1dI3 Di2i3]]]]]] :
   exists i1,
    [/\ i1 != 0, i != i1 &
     exists i2, 
       [/\ i2 != 0, i != i2, i1 != i2 &
       exists i3,
         [/\ i3 !=0, i != i3, i1 != i3 & i2 != i3]]].
  have: (4 < #|Iirr W'1|)%N by rewrite card_ord.
  rewrite (cardD1 (0: 'I__)) (cardD1 i) !inE NZi !ltnS=> HH.
  case/card_gt0P: (ltn_trans (is_true_true : 0 < 2)%N HH)=> i1.
  rewrite !inE=> Hi1; exists i1.
  case/and3P: (Hi1); rewrite 1![i1 == _]eq_sym=> -> -> _; split=> //.
  move: HH; rewrite (cardD1 i1) !inE Hi1 ltnS=> HH.
  case/card_gt0P: (ltn_trans (is_true_true : 0 < 1)%N HH)=> i2.
  rewrite !inE=> Hi2; exists i2.
  case/and4P: (Hi2); rewrite 2![i2 == _]eq_sym=> -> -> -> _; split=> //.
  move: HH; rewrite (cardD1 i2) !inE Hi2 ltnS=> /card_gt0P=> [[i3]].
  rewrite !inE=> Hi3; exists i3.
  by case/and5P: (Hi3); rewrite 3![i3 == _]eq_sym=> -> -> -> ->.
case: (dAEI NZi1 NZj' (ccTIirrE NZi1 NZj'))=> [[v v3 /=] Ai1j'].
wlog: v1 v2 v v3 Aij Ai1j' / (v == ndirr v1) && v3 '<> v2=> [WL|].
  case/or4P: (dA2_split IdI1 JdJ' Aij Ai1j'); first by apply: WL Aij Ai1j'.
  - by apply: WL (dAsr Aij) Ai1j'.
  - by apply: WL Aij (dAsr Ai1j').
  apply: WL (dAsr Aij) (dAsr Ai1j').
case/andP=> /eqP HH Dv3v2; rewrite {v}HH in Ai1j'.
case: (dAEI NZi2 NZj' (ccTIirrE NZi2 NZj'))=> [[v v4 /=] Ai2j'].
wlog: v1 v2 v v4 Dv3v2 Aij Ai1j' Ai2j' / (v == ndirr v2) && v4 '<> v1=> [WL|].
  case/or4P: (dA2_split IdI2 JdJ' Aij Ai2j').
  - case/andP=> /eqP HH DD; rewrite HH in Ai2j'.
    by case/and3P: (dA2l_diffs  I1dI2 Ai1j' Ai2j'); rewrite eqxx.
  - by apply: WL Aij Ai1j' Ai2j'.
  - case/andP=> /eqP HH DD; rewrite HH in Ai2j'.
    by case/and3P: (dA2l_diffs  I1dI2 Ai1j' Ai2j'); rewrite eqxx.
  by apply: WL Aij Ai1j' (dAsr Ai2j').
case/andP=> /eqP HH Dv3v1; rewrite {v}HH in Ai2j'.
case: (dAEI NZi3 NZj' (ccTIirrE NZi3 NZj'))=> [[v5 v6 /=] Ai3j'].
case/or4P: (dA2_split IdI3 JdJ' Aij Ai3j'); case/andP=> /eqP HH DD; 
        rewrite HH in Ai3j'.
- by case/and3P: (dA2l_diffs  I1dI3 Ai1j' Ai3j'); rewrite eqxx.
- by case/and3P: (dA2l_diffs  Di2i3 Ai2j' Ai3j'); rewrite eqxx.
- by case/and3P: (dA2l_diffs  I1dI3 Ai1j' Ai3j'); rewrite eqxx.
by case/and3P: (dA2l_diffs  Di2i3 Ai2j' Ai3j'); rewrite eqxx.
Qed.
    
End SymmetricalDecomposition.

(* Horizontal instanciation *)
Let h_beta_hyp : beta_hyp3_5 beta_.
Proof.
split; rewrite 2?(nirrW1, nirrW2, =^~ (card_ord (Nirr _))) //=.
move=> i j i' j' NZi NZj NZi' NZj'.
have [HH HH1 _] := specA NZi NZj.
split=> //; first exact: card_dirr_const_beta_diff.
  exact: card_dirr_const_beta_diffl.
exact: card_dirr_const_beta_diffr.
Qed.

(* Vertical instanciation *)
Let v_beta_hyp : beta_hyp3_5 (fun i => beta_^~ i).
Proof.
split; rewrite 2?(nirrW1, nirrW2, =^~ (card_ord (Nirr _))) //=.
move=> j i j' i' NZj NZi NZj' NZi'.
have [HH HH1 _] := specA NZi NZj.
split=> // *; first exact: card_dirr_const_beta_diff.
  exact: card_dirr_const_beta_diffr.
exact: card_dirr_const_beta_diffl.
Qed.

Local Notation hcTIirr := (ccTIirr h_beta_hyp).
Local Notation vcTIirr := (ccTIirr v_beta_hyp).
Let hcTIirrE := ccTIirrE h_beta_hyp.
Let vcTIirrE := ccTIirrE v_beta_hyp.
Let hcTIirr_inP := ccTIirr_inP h_beta_hyp.
Let hcTIirr_inN := ccTIirr_inN h_beta_hyp.
Let vcTIirr_inP := ccTIirr_inP v_beta_hyp.
Let vcTIirr_inN := ccTIirr_inN v_beta_hyp.

Let hcTIirr_diff_vcTIrr i j : i != 0 -> j != 0 -> vcTIirr i != hcTIirr j.
Proof.
move=> NZi NZj; apply/eqP=> HH.
move: w1gt2 w2gt2 coW12 oddW1 oddW2.
rewrite leq_eqVlt; case/orP=> [/eqP {1}<- |].
  rewrite leq_eqVlt; case/orP=> [/eqP {1}<- //|].
  rewrite leq_eqVlt; case/orP=> [/eqP {2}<- //|].
  rewrite -{1}nirrW2 card_ord => HW2 _ _ _.
  have [i' NZi' I'dI]: exists2 i', i' != 0 & i' != i.
    move: w1gt2; rewrite -nirrW1.
    rewrite (cardD1 (0: 'I__)) (cardD1 i) !inE NZi !ltnS=> /card_gt0P=> [[i1]].
    by rewrite !inE=> /and3P [] H1 H2 H3; exists i1.
  case/negP: (vcTIirr_inP HW2 NZj NZi' NZi I'dI).
  by rewrite HH hcTIirrE.
rewrite leq_eqVlt; case/orP=> [/eqP {2}<- //|].
rewrite -{1}nirrW1 card_ord => HW1 _ _ _.
have [j' NZj' J'dJ]: exists2 j', j' != 0 & j' != j.
  move: w2gt2; rewrite -nirrW2.
  rewrite (cardD1 (0: 'I__)) (cardD1 j) !inE NZj !ltnS => /card_gt0P=> [[j']].
  by rewrite !inE => /and3P[] H1 H2 H3; exists j'.
case/negP: (hcTIirr_inP HW1 NZi NZj' NZj J'dJ).
by rewrite -HH vcTIirrE.
Qed.

(* This is the witness for (3.5). *)
Definition dcTIirr (i : Iirr W1) (j : Iirr W2) : dIirr G := 
  let v i := ndirr (vcTIirr i) in
  let h j := ndirr (hcTIirr j) in
  if (i == 0) then 
    if (j == 0) then dirr1 G else h j
  else
    if (j == 0) then v i else
      dirr_dIirr (fun i => beta_ i j + dchi (h j) + dchi (v i)) i.

Local Notation xi_ i j := (dchi (dcTIirr i j)).

Lemma dcTIrrE i j :
  i != 0 -> j != 0 -> beta_ i j = - xi_ i 0 - xi_ 0 j + xi_ i j.
Proof.
move=> NZi NZj.
rewrite /dcTIirr !eqxx (negPf NZi) (negPf NZj).
pose TT := @dirr_dIirrPE _ _ _ _ (fun j => j != 0).
rewrite TT //; first by rewrite addrC !addrA !addrK.
move=> i1 NZi1.
case: (dirr_small_norm (beta_vchar i1 j) (cfnorm_beta NZi1 NZj)) => //.
move=> Acar _ ->; move/eqP: Acar; rewrite !dchi_ndirrE.
set h := hcTIirr j; set v := vcTIirr i1; rewrite addrAC addrC addrA addrC.
rewrite (cardsD1 h) (big_setD1 h) hcTIirrE // addKr eqSS.
have A'u_v: v \in A_ i1 j :\ h by rewrite 2!inE hcTIirr_diff_vcTIrr ?vcTIirrE.
rewrite (cardsD1 v) (big_setD1 v) A'u_v ?addKr // => /cards1P[w ->].
by rewrite big_set1 dirr_dchi.
Qed.

Lemma dcTIrrDE i j : i != 0 -> j != 0 -> 
  A_ i j = [set ndirr (dcTIirr i 0); ndirr (dcTIirr 0 j); dcTIirr i j].
Proof.
by move=> NZi NZj; apply: dirr_const_beta_inv; rewrite // !dchi_ndirrE -dcTIrrE.
Qed.

Lemma beta'1 i j : i != 0 -> j != 0 -> dirr1 G \notin dirr_constt (beta_ i j).
Proof. by move=> NZi NZj; rewrite inE dchi1 cfdot_beta_1 ?ltrr. Qed.

Lemma beta'N1 i j : i != 0 -> j != 0 -> 
  ndirr (dirr1 G) \notin dirr_constt (beta_ i j).
Proof.
move=> NZi NZj; rewrite inE dchi_ndirrE dchi1 cfdotNr cfdot_beta_1 //.
by rewrite oppr0 ltrr.
Qed.

Lemma dcTIirr_vchar i j : xi_ i j \in 'Z[irr G].
Proof. by apply: dchi_vchar. Qed.

(* This is first part of Peterfalvi (3.5). *)
Lemma cfdot_dcTIirr i j i' j' : 
  '[xi_ i j, xi_ i' j'] = ((i == i') && (j == j'))%:R.
Proof.
move: i j i' j'.
pose i1 : Iirr W1 := inZp 1.
pose j1 : Iirr W2 := inZp 1.
have NZi1 : i1 != 0 by rewrite -val_eqE /= NirrW1 -(subnKC w1gt2).
have NZj1 : j1 != 0 by rewrite -val_eqE /= NirrW2 -(subnKC w2gt2).
have P0 : xi_ 0 0 = 1 by rewrite {1}/dcTIirr !eqxx dchi1 .
have Pnorm i j : '[xi_ i j] == 1 by rewrite cfnorm_dchi.
have Pvchar := dcTIirr_vchar.
have PC i j i' j' : '[xi_ i j, xi_ i' j'] = '[xi_ i' j', xi_ i j].
  do 2 rewrite cfdot_dchi //; rewrite ![dcTIirr i' j' == _]eq_sym.
  congr (_ - _); rewrite -{1}[_ i j]ndirrK.
  case: (_ =P _)=> [/ndirr_inj ->|HH]; first by rewrite eqxx.
  by case: (_ =P _)=> // HH1; case: HH; rewrite HH1.
have ndirrEK (G1 : {group gT}) (i j : dIirr G1)  : 
   (ndirr i == ndirr j) = (i == j).
  by apply/eqP/eqP=> [/ndirr_inj|->].
have ndirrSK (G1 : {group gT}) (i j : dIirr G1)  : 
   (ndirr i == j) = (i == ndirr j).
  by rewrite -{2}[i]ndirrK ndirrEK.
have P1 i j : '[1, xi_ i j] == ((i == 0) && (j == 0))%:R.
  rewrite -dchi1 cfdot_dchi.
  case: (boolP (i == 0))=> [/eqP-> | NZi];
       case: (boolP (j == 0))=> [/eqP-> | NZj].
  - by rewrite /dcTIirr !eqxx [dirr1 _ == _]eq_sym (negPf (ndirr_diff _)) subr0.
  - move: (beta'N1 NZi1 NZj) (beta'1 NZi1 NZj). 
    rewrite (dcTIrrDE NZi1 NZj) !{1}inE !negb_or !ndirrEK -!andbA. 
    by case/and3P => _ /negPf-> _ /and3P [_ /negPf-> _]; rewrite subrr.
  - move: (beta'N1 NZi NZj1) (beta'1 NZi NZj1). 
    rewrite (dcTIrrDE NZi NZj1) !{1}inE !negb_or !ndirrEK -!andbA. 
    case/and3P => /negPf HH1 _ _ /and3P [/negPf HH2 _ _].
    by rewrite HH1 HH2 subrr.
  move: (beta'N1 NZi NZj) (beta'1 NZi NZj). 
  rewrite (dcTIrrDE NZi NZj) !{1}inE !negb_or !ndirrEK -!andbA. 
  case/and3P => _ _ /negPf HH1 /and3P [_ _ /negPf HH2].
  by rewrite -{2}[dirr1 G]ndirrK ndirrEK HH1 HH2 subrr.
have TT i2 j2 (NZi2 : i2 != 0) (NZj2 : j2 != 0) :
   [&& i2 != 0 , j2 != 0 &  
       dirr_constt (beta_ i2 j2) ==
       [set ndirr (dcTIirr i2 0); ndirr (dcTIirr 0 j2); dcTIirr i2 j2]].
  by rewrite NZi2 NZj2 /=; apply/eqP; apply: dcTIrrDE.
have Pjj' j j' : '[xi_ 0 j, xi_ 0 j'] == (j == j')%:R.
  case: (boolP (j == j')) => [/eqP->|]; first by rewrite Pnorm.
  case: (boolP (j == 0)) => [/eqP->| NZj] JdJ'.
    by rewrite P0 (eqP (P1 _ _)) [j' == _]eq_sym (negPf JdJ') eqxx.
  case: (boolP (j' == 0)) => [/eqP->| NZj'].
    by rewrite PC P0 (eqP (P1 _ _)) (negPf NZj) eqxx.
  move: (dA2r_diff h_beta_hyp JdJ' (TT _ _ NZi1 NZj) (TT _ _ NZi1 NZj')).
  by rewrite cfdot_dchi !ndirrEK => /andP [/negPf-> /negPf->]; rewrite subrr.
have Pii' i i' : '[xi_ i 0, xi_ i' 0] == (i == i')%:R.
  case: (boolP (i == i')) => [/eqP->|]; first by rewrite Pnorm.
  case: (boolP (i == 0)) => [/eqP->| NZi] IdI'.
    by rewrite P0 (eqP (P1 _ _)) [i' == _]eq_sym (negPf IdI') eqxx.
  case: (boolP (i' == 0)) => [/eqP->| NZi'].
    by rewrite PC P0 (eqP (P1 _ _)) (negPf NZi) eqxx.
  move: (dA2l_diff h_beta_hyp IdI' (dAsl (TT _ _ NZi NZj1))
             (dAsl (TT _ _ NZi' NZj1))).
  by rewrite cfdot_dchi !ndirrEK => /andP [/negPf-> /negPf->]; rewrite subrr.
have Pij i j : '[xi_ i 0, xi_ 0 j] == ((i == 0) && (j == 0))%:R.
  case: (boolP (i == 0))=> [/eqP-> | NZi]; first by rewrite P0 (eqP (P1 _ _)).
  case: (boolP (j == 0))=> [/eqP-> | NZj].
    by rewrite PC P0 (eqP (P1 _ _)) (negPf NZi) eqxx.
  case/andP: (dA_diff h_beta_hyp (TT _ _ NZi NZj)).
  by rewrite cfdot_dchi !ndirrEK => /negPf-> /negPf->; rewrite subrr.
have Pii'j i i' j : '[xi_ i 0, xi_ i' j] == ((i == i') && (j == 0))%:R.
  case: (boolP (i == 0))=> [/eqP-> // | NZi].
    by rewrite P0 (eqP (P1 _ _)) ![0 == _]eq_sym.
  case: (boolP (i' == 0))=> [/eqP-> // | NZi'].
  case: (boolP (j == 0))=> [/eqP-> // | NZj]; first by rewrite andbT Pii'.
  rewrite andbF.
  case: (boolP (i == i'))=> [/eqP<- | IdI'].
    case/andP: (dA_diff h_beta_hyp (dAsr (TT _ _ NZi NZj))).
    by rewrite cfdot_dchi !ndirrSK ndirrK => /negPf-> /negPf->; rewrite subrr.
  case/andP: (dA2l_diff h_beta_hyp IdI' (dAsl (TT _ _ NZi NZj))
                (dAsr (dAsl (TT _ _ NZi' NZj)))).
  by rewrite cfdot_dchi !ndirrSK ndirrK => /negPf-> /negPf->; rewrite subrr.
have Pijj' i j j' : '[xi_ 0 j, xi_ i j'] == ((i == 0) && (j == j'))%:R.
  case: (boolP (j == 0))=> [/eqP-> // | NZj].
    by rewrite P0 (eqP (P1 _ _)) ![0 == _]eq_sym.
  case: (boolP (i == 0))=> [/eqP-> // | NZi].
    by rewrite (eqP (Pjj' _ _)).
  case: (boolP (j' == 0))=> [/eqP-> // | NZj'].
    by rewrite PC // (eqP (Pij _ _)) (negPf NZi).
  case: (boolP (j == j'))=> [/eqP<- | JdJ'].
    case/andP: (dA_diff h_beta_hyp (dAsr (dAsl (TT _ _ NZi NZj)))).
    by rewrite cfdot_dchi !ndirrSK ndirrK => /negPf-> /negPf->; rewrite subrr.
  case/andP: (dA2r_diff h_beta_hyp JdJ' (TT _ _ NZi NZj)
                (dAsr (TT _ _ NZi NZj'))).
  by rewrite cfdot_dchi !ndirrSK ndirrK => /negPf-> /negPf->; rewrite subrr.
move=> i j i' j'; apply/eqP.
case: (boolP (i == 0))=> [/eqP-> // | NZi].
  by rewrite [0 == _]eq_sym; apply: Pijj'.
case: (boolP (i' == 0))=> [/eqP-> // | NZi'].
  by rewrite PC [j == _]eq_sym; apply: Pijj'.
case: (boolP (j == 0))=> [/eqP-> | NZj].
  by rewrite (eqP (Pii'j _ _ _)) [0 == _]eq_sym.
case: (boolP (j' == 0))=> [/eqP-> | NZj'].
  by rewrite PC (eqP (Pii'j _ _ _)) [i == _]eq_sym.
case: (boolP (i == _))=> [/eqP<- | IdI'].
  case: (boolP (j == _))=> [/eqP<- // | JdJ'].
  case/andP: (dA2r_diff h_beta_hyp JdJ' (dAsr (TT _ _ NZi NZj))
                (dAsr (TT _ _ NZi NZj'))).
  by rewrite cfdot_dchi => /negPf-> /negPf->; rewrite subrr.
case: (boolP (j == _))=> [/eqP<- // | JdJ'].
  case/andP: (dA2l_diff h_beta_hyp IdI' (dAsr (dAsl (TT _ _ NZi NZj)))
                (dAsr (dAsl (TT _ _ NZi' NZj)))).
  by rewrite cfdot_dchi => /negPf-> /negPf->; rewrite subrr.
rewrite cfdot_dchi.
case: (boolP (_ j == _))=> [/eqP H1|_].
  have F1 := dAr (TT _ _ NZi NZj).
  have := dAr (TT _ _ NZi' NZj'); rewrite -H1 => F2.
  case/or4P: (dA2_split h_beta_hyp IdI' JdJ' F1 F2)=> /and3P [];
      rewrite ndirrK subr_eq0 => [/eqP H2 _ _].
  - move: (Pii' i i'); rewrite cfdot_dchi -H2 eqxx.
    by rewrite (negPf (ndirr_diff _)) (negPf IdI') subr_eq0 eq_sym oner_eq0.
  - move: (Pij i' j); rewrite cfdot_dchi -H2 ndirrK eqxx.
    rewrite [_ 0 == _]eq_sym (negPf (ndirr_diff _)) (negPf NZi') (negPf NZj).
    by rewrite  subr_eq0 eq_sym oner_eq0.
  - move: (Pij i j'); rewrite cfdot_dchi -H2 eqxx ndirrSK.
    rewrite [_ j' == _]eq_sym (negPf (ndirr_diff _)) (negPf NZi) (negPf NZj').
    by rewrite  subr_eq0 eq_sym oner_eq0.
  move: (Pjj' j j'); rewrite cfdot_dchi -H2 eqxx.
  by rewrite (negPf (ndirr_diff _)) (negPf JdJ') subr_eq0 eq_sym oner_eq0.
case: (boolP (_ j == _))=> [/eqP H1|_]; last by rewrite subrr.
have F1 := dAr (TT _ _ NZi NZj).
have := dAr (TT _ _ NZi' NZj'); rewrite -[dcTIirr i' j']ndirrK -{1}H1 => F2.
case/or4P: (dA2_n_split h_beta_hyp IdI' JdJ' F1 F2)=> /and3P [];
      rewrite ?(ndirrEK, ndirrK) subr_eq0 => [/eqP H2 _ _].
- move: (Pii' i i'); rewrite cfdot_dchi -H2 eqxx.
  rewrite [_ 0 == _]eq_sym (negPf (ndirr_diff _)) (negPf IdI').
  by rewrite subr0 eqr_nat.
- move: (Pij i' j); rewrite cfdot_dchi -H2 eqxx.
  rewrite [_ 0 == _]eq_sym (negPf (ndirr_diff _)) (negPf NZi') (negPf NZj).
  by rewrite  subr0 eqr_nat.
- move: (Pij i j'); rewrite cfdot_dchi -H2 eqxx.
  rewrite [_ j' == _]eq_sym (negPf (ndirr_diff _)) (negPf NZi) (negPf NZj').
  by rewrite  subr0 eqr_nat.
move: (Pjj' j j'); rewrite cfdot_dchi -H2 eqxx.
rewrite [_ j' == _]eq_sym (negPf (ndirr_diff _)) (negPf JdJ').
by rewrite subr0 eqr_nat.
Qed.

(* This is second_part of PeterFalvi (3.5). *)
Lemma dcTIirrE i j : i != 0 -> j != 0 ->
  'Ind[G] (alpha_ i j) = 1 - xi_ i 0 - xi_ 0 j + xi_ i j.
Proof. by move=> NZi NZj; rewrite -!addrA addrC addrA -dcTIrrE // subrK. Qed.

End BetaDecomposition.

Local Notation xi_ i j := (dchi (dcTIirr i j)).

Fact cyclicTIiso_key : unit. Proof. by []. Qed.
Definition cyclicTIiso_def of cyclicTI_hypothesis G defW :=
   let sigma (f : {ffun Iirr W -> dIirr G}) :=
     sval (linear_of_free (irr W) [seq dchi (f k) | k : Iirr W]) in
   let sigma_spec f :=
     [&& orthonormal (map (sigma f) (irr W)), sigma f 1 == 1
       & ('CF(W, V) <= lker (linfun (sigma f) - linfun 'Ind[G]))%VS] in
   oapp sigma [linear of \0] [pick f | sigma_spec f].
Definition cyclicTIiso : {linear 'CF(W) -> 'CF(G)} :=
  locked_with cyclicTIiso_key (cyclicTIiso_def ctiW).

Local Notation sigma := cyclicTIiso.
Let im_sigma := map sigma (irr W).
Let eta_ i j := sigma (w_ i j).

(* This is PeterFalvi (3.2) (a, b, c). *)
Lemma cyclicTIiso_spec :
  [/\ {in 'Z[irr W], isometry sigma, to 'Z[irr G]},
      sigma 1 = 1 &
      {in 'CF(W, V), forall phi : 'CF(W), sigma phi = 'Ind[G] phi}].
Proof.
rewrite [sigma]unlock /cyclicTIiso_def; case: pickP => [/= f /and3P[]|].
  case: linear_of_free => /= sigma Dsigma o1sigma /eqP-> /eqlfun_inP sigmaV.
  split=> // [| phi /sigmaV]; last by rewrite !lfunE.
  do [rewrite size_map !size_tuple => /(_ (irr_free W) (card_ord _))] in Dsigma.
  have [inj_sigma dot_sigma] := orthonormalP o1sigma.
  rewrite -(map_tnth_enum (irr W)) -map_comp in Dsigma inj_sigma.
  move/eq_in_map in Dsigma; move/injectiveP in inj_sigma.
  split=> [|_ /zchar_tuple_expansion[z Zz ->]].
    apply: isometry_in_zchar=> _ _ /irrP[k1 ->] /irrP[k2 ->].
    by rewrite dot_sigma ?map_f ?mem_irr // cfdot_irr (inj_eq inj_sigma).
  rewrite linear_sum rpred_sum // => k _; rewrite linearZ rpredZ_Cint //=.
  by rewrite -tnth_nth [sigma _]Dsigma ?mem_enum ?dchi_vchar.
pose f := [ffun k => prod_curry dcTIirr (inv_dprod_Iirr defW k)] => /(_ f).
case: (linear_of_free _ _) => /= sigma Dsigma /and3P[].
have{Dsigma} Deta i j: sigma (w_ i j) = xi_ i j.
  rewrite /w_ -tnth_map /= (tnth_nth 0) /=.
  rewrite Dsigma ?irr_free //; last by rewrite !size_tuple card_ord.
  by rewrite nth_mktuple ffunE dprod_IirrK.
have sigma1: sigma 1 = 1 by rewrite -w_00 Deta /dcTIirr !eqxx dchi1.
split; last 2 [by rewrite sigma1].
  rewrite map_orthonormal ?irr_orthonormal //; apply: isometry_in_zchar.
  move=> _ _ /cycTIirrP[i1 [j1 ->]] /cycTIirrP[i2 [j2 ->]] /=.
  by rewrite !Deta cfdot_dcTIirr cfdot_w.
rewrite -(span_basis cfWVbasis).
apply/span_subvP=> _ /imageP[[i j] /setXP[/= nzi nzj] ->].
rewrite memv_ker !lfun_simp /= subr_eq0 {1}alphaE linearD !linearB sigma1 !Deta.
by rewrite dcTIirrE //; rewrite !inE in nzi nzj.
Qed.

Lemma cycTI_Zisometry : {in 'Z[irr W], isometry sigma, to 'Z[irr G]}.
Proof. by case: cyclicTIiso_spec. Qed.

Let Isigma : {in 'Z[irr W] &, isometry sigma}.
Proof. by case: cycTI_Zisometry. Qed.
Let Zsigma : {in 'Z[irr W], forall phi, sigma phi \in 'Z[irr G]}.
Proof. by case: cycTI_Zisometry. Qed.

Lemma cycTIisometry : isometry sigma.
Proof.
move=> phi psi; have [[a ->] [b ->]] := (cfun_irr_sum phi, cfun_irr_sum psi).
rewrite !linear_sum !cfdot_suml; apply: eq_bigr => i _.
rewrite !cfdot_sumr; apply: eq_bigr => j _.
by rewrite !linearZ !cfdotZl !cfdotZr /= Isigma ?irr_vchar.
Qed.

Lemma cycTIiso_vchar i j : eta_ i j \in 'Z[irr G].
Proof. by rewrite Zsigma ?irr_vchar. Qed.

Lemma cfdot_cycTIiso i1 i2 j1 j2 : 
  '[eta_ i1 j1, eta_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
Proof. by rewrite cycTIisometry. Qed.

Lemma cfnorm_cycTIiso i j : '[eta_ i j] = 1.
Proof. by rewrite cycTIisometry cfnorm_irr. Qed.

Lemma cycTIiso_dirr i j : sigma (w_ i j) \in dirr G.
Proof. by rewrite dirrE cycTIiso_vchar /= cfnorm_cycTIiso. Qed.

Lemma cycTIiso_orthonormal : orthonormal im_sigma.
Proof. by rewrite map_orthonormal ?irr_orthonormal. Qed.

Lemma cycTIiso_eqE i1 i2 j1 j2 :
  (eta_ i1 j1 == eta_ i2 j2) = ((i1 == i2) && (j1 == j2)).
Proof.
have /inj_in_eq-> := Zisometry_inj Isigma; try exact: irr_vchar.
by rewrite (inj_eq irr_inj) (inj_eq (dprod_Iirr_inj _)).
Qed.

Lemma cycTIiso_neqN i1 i2 j1 j2 : (eta_ i1 j1 == - eta_ i2 j2) = false.
Proof.
rewrite -addr_eq0; apply/eqP=> /(congr1 (cfdot (eta_ i1 j1)))/eqP.
by rewrite cfdot0r cfdotDr !cfdot_cycTIiso !eqxx -mulrS pnatr_eq0.
Qed.

Lemma cycTIiso1 : sigma 1 = 1.
Proof. by case: cyclicTIiso_spec. Qed.

Lemma cycTIiso_Ind : {in 'CF(W, V), forall phi, sigma phi = 'Ind[G, W] phi}.
Proof. by case: cyclicTIiso_spec. Qed.

Let sigma_Res_V :
  [/\ forall phi, {in V, sigma phi =1 phi}
    & forall psi : 'CF(G), orthogonal psi im_sigma -> {in V, psi =1 \0}].
Proof.
have sigW i j : '[sigma 'chi_i, sigma 'chi_j] = (i == j)%:R.
  by rewrite cycTIisometry cfdot_irr.
have [j | sigmaV sigma'V] := equiv_restrict_compl_ortho sWG nsVW cfWVbasis sigW.
  rewrite /= -/cfWVbase -(eq_bigr _ (fun _ _ => linearZ _ _)) /= -linear_sum.
  rewrite -cfun_sum_cfdot cycTIiso_Ind //.
  by rewrite (basis_mem cfWVbasis) ?mem_nth ?size_image.
split=> [phi v Vv | psi /orthoPl o_psi_sigma].
  rewrite [phi]cfun_sum_cfdot linear_sum !sum_cfunE.
  by apply: eq_bigr => k _; rewrite linearZ !cfunE sigmaV.
by apply: sigma'V => k; rewrite o_psi_sigma ?map_f ?mem_irr.
Qed.

(* This is Peterfalvi (3.2)(d). *)
Lemma cycTIiso_restrict phi : {in V, sigma phi =1 phi}.
Proof. by case: sigma_Res_V. Qed.

(* This is Peterfalvi (3.2)(e). *)
Lemma ortho_cycTIiso_vanish (psi : 'CF(G)) : 
  orthogonal psi im_sigma -> {in V, forall x, psi x = 0}.
Proof. by case: sigma_Res_V psi. Qed.

(* This is PeterFalvi (3.7). *)
Lemma cycTIiso_cfdot_exchange (psi : 'CF(G)) i1 i2 j1 j2 :
    {in V, forall x, psi x = 0} -> 
  '[psi, eta_ i1 j1] + '[psi, eta_ i2 j2]
     = '[psi, eta_ i1 j2] + '[psi, eta_ i2 j1].
Proof.
move=> psiV_0; pose phi : 'CF(W) := w_ i1 j1 + w_ i2 j2 - w_ i1 j2 - w_ i2 j1.
have Vphi: phi \in 'CF(W, V).
  apply/cfun_onP=> g; rewrite inE negb_and negbK !inE orbC.
  case/or3P=> [/cfun0-> // | W1g | W2g]; apply/eqP; rewrite !cfunE subr_eq0.
    by rewrite addrC -[g]mulg1 /w_ !dprod_IirrE !cfDprodE ?lin_char1 ?addKr.
  by rewrite -[g]mul1g /w_ !dprod_IirrE !cfDprodE ?lin_char1 ?addrK.
suffices: '[psi, 'Ind[G] phi] == 0.
  rewrite -!cycTIiso_Ind // !linearB !linearD !cfdotBr !cfdotDr.
  by rewrite -addrA -opprD subr_eq0 => /eqP.
rewrite (cfdotEr _ (cfInd_on sWG Vphi)) big1 ?mulr0 //.
by move=> _ /imset2P[x y Vx Gy ->]; rewrite cfunJ ?psiV_0 ?mul0r.
Qed.

(* This is NC as defined in PeterFalvi (3.6). *)
Definition cyclicTI_NC phi := #|[set ij | '[phi, eta_ ij.1 ij.2] != 0]|.
Local Notation NC := cyclicTI_NC.

Lemma cycTI_NC_opp (phi : 'CF(G)) : (NC (- phi)%R = NC phi)%N.
Proof. by apply: eq_card=> [[i j]]; rewrite !inE cfdotNl oppr_eq0. Qed.

Lemma cycTI_NC_sign (phi : 'CF(G)) n : (NC ((-1) ^+ n *: phi)%R = NC phi)%N.
Proof. 
elim: n=> [|n IH]; rewrite ?(expr0,scale1r) //.
by rewrite exprS -scalerA scaleN1r cycTI_NC_opp.
Qed.

Lemma cycTI_NC_iso i j : NC (eta_ i j) = 1%N.
Proof.
rewrite -(cards1 (i, j)); apply: eq_card => [[i1 j1]]; rewrite !inE /=.
rewrite cfdot_cycTIiso //= pnatr_eq0 (can_eq oddb _ false) eqbF_neg negbK.
by rewrite -xpair_eqE eq_sym.
Qed.

Lemma cycTI_NC_irr i : (NC 'chi_i <= 1)%N.
Proof.
apply: wlog_neg; rewrite -ltnNge => /ltnW/card_gt0P[[i1 j1]].
rewrite inE cfdot_dirr ?(mem_dirr, cycTIiso_dirr) //=.
case: ('chi_i =P _) => [-> | _]; first by rewrite cycTI_NC_opp cycTI_NC_iso.
by case: ('chi_i =P _)=> [-> | _]; rewrite (cycTI_NC_iso, eqxx).
Qed.

Lemma cycTI_NC_dirr f : f \in dirr G -> (NC f <= 1)%N.
Proof. by case/dirrP=> b [i ->]; rewrite cycTI_NC_sign cycTI_NC_irr. Qed.

Lemma cycTI_NC_dchi di : (NC (dchi di) <= 1)%N.
Proof. by rewrite cycTI_NC_dirr ?dirr_dchi. Qed.

Lemma cycTI_NC_0 : NC 0 = 0%N.
Proof. by apply: eq_card0 => ij; rewrite !inE cfdot0l eqxx. Qed.

Lemma cycTI_NC_add n1 n2 phi1 phi2 :
  (NC phi1 <= n1 -> NC phi2 <= n2 -> NC (phi1 + phi2)%R <= n1 + n2)%N.
Proof.
move=> ub1 ub2; apply: leq_trans {ub1 ub2}(leq_add ub1 ub2).
rewrite -cardsUI -[NC _]addn0 leq_add // subset_leq_card //.
apply/subsetP=> [[i j]]; rewrite !inE /= -negb_and cfdotDl.
by apply: contra => /andP[/eqP-> /eqP->]; rewrite addr0.
Qed.

Lemma cycTI_NC_sub n1 n2 phi1 phi2 :
  (NC phi1 <= n1 -> NC phi2 <= n2 -> NC (phi1 - phi2)%R <= n1 + n2)%N.
Proof. by move=> ub1 ub2; rewrite cycTI_NC_add ?cycTI_NC_opp. Qed. 

Lemma cycTI_NC_scale_nz a phi : a != 0 -> NC (a *: phi) = NC phi.
Proof.
move=> nz_a; apply: eq_card => ij.
by rewrite !inE cfdotZl mulf_eq0 negb_or nz_a.
Qed.

Lemma cycTI_NC_scale a phi n : (NC phi <= n -> NC (a *: phi) <= n)%N.
Proof.
have [-> _ | /cycTI_NC_scale_nz-> //] := eqVneq a 0.
by rewrite scale0r cycTI_NC_0.
Qed.

Lemma cycTI_NC_norm phi n :
  phi \in 'Z[irr G] -> '[phi] <= n%:R -> (NC phi <= n)%N.
Proof.
move=> Zphi ub_phi; apply: leq_trans (_ : #|dirr_constt phi| <= n)%N.
  rewrite {1}[phi]cfun_sum_dconstt // -sum1_card.
  elim/big_rec2: _ => [|/= i n1 phi1 _]; first by rewrite cycTI_NC_0.
  by apply: cycTI_NC_add; rewrite cycTI_NC_scale ?cycTI_NC_dchi.
rewrite -leC_nat (ler_trans _ ub_phi) ?cnorm_dconstt // -sumr_const.
apply: ler_sum => i phi_i; rewrite sqr_Cint_ge1 ?Cint_Cnat ?Cnat_dirr //.
by rewrite gtr_eqF -?dirr_consttE.
Qed.

(* This is PeterFalvi (3.8). *)
Lemma small_cycTI_NC (phi : 'CF(G)) i j : 
  {in V, forall x, phi x = 0} -> (NC phi < 2 * minn w1 w2)%N ->
  '[phi, sigma (w_ i j)] != 0 ->    
   {(forall i1 j1,
      '[phi, sigma (w_ i1 j1)] = (j == j1)%:R * '[phi, sigma (w_ i j)])}
   +
   {(forall i1 j1 ,
      '[phi, sigma (w_ i1 j1)] = (i == i1)%:R * '[phi, sigma (w_ i j)])}.
Proof.
move=> phiV_0 NC_M NZaij.
pose a i j := '[phi, sigma (w_ i j)].
have CDS i2 j2 i1 j1 : a i1 j1 = a i1 j2 + a i2 j1 - a i2 j2.
  by rewrite cycTIiso_cfdot_exchange ?addrK.
pose S := [set ij | a ij.1 ij.2 != 0].
pose L j := [set ij | ij.2 == j] :&: S.
pose C i := [set ij | ij.1 == i] :&: S.
have LsS j1 : C j1 \subset S by apply: subsetIr.
have CsS i1 : L i1 \subset S by apply: subsetIr.
have LI i1 i2 : L i1 :&: L i2 = if i1 == i2 then L i1 else set0.
  apply/setP=> [[i3 j3]]; have [-> | i2'1] := altP eqP; first by rewrite setIid.
  by rewrite -setIIl !inE /= -andbA; apply/and3P=> [[/eqP-> /idPn[]]].
have CI i1 i2 : C i1 :&: C i2 = if i1 == i2 then C i1 else set0.
  apply/setP=> [[i3 j3]]; have [-> | i2'1] := altP eqP; first by rewrite setIid.
  by rewrite -setIIl !inE /= -andbA; apply/and3P=> [[/eqP-> /idPn[]]].
have LCI i1 j1 : (L j1 :&: C i1) \subset [set (i1,j1)].
  apply/subsetP=> [[i2 j2]]; rewrite !inE /=.
  by case/andP=> /andP [/eqP-> _] /andP [/eqP-> _].
have FC i1: (forall j, a i1 j != 0) -> #|C i1| = w2.
  move=> FF; transitivity #|[seq (i1, j) | j : Iirr W2]|; last first.
    by rewrite card_in_image // => i3 i4 _ _ /= [].
  apply: eq_card=> [[i3 j3]]; rewrite !inE /=.
  by apply/andP/codomP=> [[/eqP-> _] | [j4 [-> ->]] //]; exists j3.
have ub_minW12: (2 * minn w1 w2 <= w1 + w2 - 2)%N.
  rewrite -(leq_add2r 2) subnK; last by rewrite -(subnKC w1gt2).
  rewrite addn2 mul2n -ltnS odd_geq /= ?odd_add ?oddW1 ?oddW2 // uphalf_double.
  rewrite -addn_min_max -addnn leq_add2l gtn_min !leq_max !ltnn orbF //=.
  by rewrite -neq_ltn.
  (* This is step 3.8.1. *)
have EqI i1 i2 j1 j2 : a i1 j2 == 0 -> a i2 j1 == 0 -> a i1 j1 == 0.
  have [-> // | i2'1] := eqVneq i1 i2.
  have [-> // | j2'1] := eqVneq j1 j2 => /eqP a12_0 /eqP a21_0.
  apply: contraLR NC_M => nz_a11; rewrite -leqNgt.
  pose LS := [set (i3, if a i3 j1 == 0 then j2 else j1) | i3 : Iirr W1].
  have LSsS: LS \subset S.
    apply/subsetP=> _ /imsetP[i3 _ ->]; rewrite inE /=.
    case: ifPn => // /eqP a31_0; apply: contraNneq nz_a11 => a32_0.
    by rewrite (CDS i3 j2) a32_0 a31_0 addrK a12_0.
  have cardLS: #|LS| = w1 by rewrite card_imset // => i3 i4 [].
  pose CS := [set (if a i1 j3 == 0 then i2 else i1, j3) | j3 : Iirr W2].
  have CSsS : CS \subset S.
    apply/subsetP=> _ /imsetP[j3 _ ->]; rewrite inE /=.
    case: ifPn => // /eqP a13_0; apply: contraNneq nz_a11 => a23_0.
    by rewrite (CDS i2 j3) a23_0 a13_0 a21_0 addrK.
  have cardCS: #|CS| = w2 by rewrite card_imset // => j3 j4 [].
  have /subset_leq_card lbS: LS :|: CS \subset S by apply/subUsetP.
  apply: leq_trans ub_minW12 (leq_trans _ lbS); rewrite cardsU cardLS cardCS.
  have <-: #|[set (i1, j1); (i2, j2)]| = 2.
    by rewrite cards2 xpair_eqE (negPf i2'1).
  apply/leq_sub2l/subset_leq_card/subsetP.
  move=> _ /setIP[/imsetP[i3 _ ->] /imsetP[j3 _] []].
  by case: ifP => _ -> _; rewrite !inE ?a21_0 ?eqxx ?orbT // ifN ?eqxx.
have cardLE i1 j1 j2 : a i1 j1 != 0 -> a i1 j2 == 0 -> #|L j1| = w1.
  move=> nz_a11 a12_0; transitivity #|[set (i2, j1) | i2 : Iirr W1]|.
    apply: eq_card => [[i3 j3]]; rewrite !inE /=.
    apply/andP/imsetP=> [[/eqP-> _] | [i2 _ [-> ->]]]; first by exists i3.
    by rewrite (contra _ nz_a11) //; apply: EqI a12_0.
  by rewrite card_imset // => i2 i3 [].
  have cardCE i1 i2 j1 : a i1 j1 != 0 -> a i2 j1 == 0 -> #|C i1| = w2.
  move=> nz_a11 a21_0; transitivity #|[set (i1, j2) | j2 : Iirr W2]|.
    apply: eq_card => [[i3 j3]]; rewrite !inE /=.
    apply/andP/imsetP=> [[/eqP-> _] | [j2 _ [-> ->]]]; first by exists j3.
    by rewrite (contra _ nz_a11) // => /EqI/(_ a21_0).
  by rewrite card_imset // => j2 j3 [].
have BLe i1 j1: (2 * minn w1 w2 <= w1 + w2 - #|L j1 :&: C i1|)%N.
  apply: leq_trans ub_minW12 (leq_sub2l _ _); apply: leqW.
  rewrite -(cards1 (i1, j1)) -setIIl subset_leq_card //.
  by apply/subsetP=> [[i2 j2] /setIP[]]; rewrite !inE andbC.
have [Ci_0 | nz_Ci] := boolP [exists j1, a i j1 == 0]; [left | right].
  (* This is step 3.8.2. *)
  have{Ci_0} [j1 ai_j1_0] := existsP Ci_0.
  have j'j1 : j1 != j by apply: contraNneq NZaij => <-.
  have defCi: C i = [set (i, j)].
    apply/setP=> [[i2 j2]]; rewrite !inE; apply: andb_id2l => /eqP-> /=.
    apply/idP/eqP=> [nz_ai_j2 | -> //]; apply: contraTeq NC_M => j'j2.
    have /subset_leq_card: L j :|: L j2 \subset S by apply/subUsetP.
    rewrite -leqNgt cardsU LI ifN_eqC // cards0 subn0; apply: leq_trans.
    by rewrite !(cardLE i _ j1) // addnn mul2n leq_double geq_minl.
  suffices HL i2 j2: j != j2 -> a i2 j2 = 0.
    move=> i2 j2; rewrite -!/(a _ _) mulr_natl mulrb.
    case: ifPn => [/eqP <- | /HL//]; have [-> // | i'i2] := eqVneq i2 i.
    by rewrite (CDS i j1) (eqP ai_j1_0) subr0 HL ?add0r // eq_sym.
  move=> j2'j; apply: contraTeq NC_M => nz_a22; rewrite -leqNgt.
  have cardC: #|C i2| = w2.
    have: (i, j2) \notin C i by rewrite defCi !inE eq_sym xpair_eqE eqxx.
    by rewrite !inE eqxx negbK => /cardCE->.
  have cardL: #|L j| = w1  by apply: (cardLE _ _ j1 NZaij).
  have /subset_leq_card: L j :|: C i2 \subset S by apply/subUsetP.
  by apply: leq_trans; rewrite cardsU cardC cardL.
 (* This is step 3.8.3. *)
do [rewrite negb_exists => /forallP/=] in nz_Ci.
suff HL i1 j1: i != i1 -> a i1 j1 = 0.
  move=> i1 j1; rewrite -!/(a _ _) mulr_natl mulrb.
  case: ifPn => [/eqP <- | /HL//]; have [-> // | j'j1] := eqVneq j1 j.
  have: (2 < #|Iirr W1|)%N by rewrite nirrW1. 
  rewrite (cardD1 i) !inE !ltnS => /leqW/card_gt0P[i2 /andP[/= i'i2 _]].
  by rewrite (CDS i2 j) !(HL i2) ?addrK // eq_sym.
move=> i1'i; apply: contraTeq NC_M => nz_a11; rewrite -leqNgt.
have [/existsP[j2 a12_0] | ] := boolP [exists j2, a i1 j2 == 0].
  have /subset_leq_card: L j1 :|: C i \subset S by apply/subUsetP.
  by apply: leq_trans; rewrite cardsU FC // !(cardLE _ _ _ _ a12_0).
rewrite negb_exists => /forallP nz_Ci1.
have /subset_leq_card: C i :|: C i1 \subset S by apply/subUsetP.
apply: leq_trans; rewrite cardsU !FC // CI ifN // cards0 subn0.
by rewrite mul2n addnn leq_double geq_minr.
Qed.

(* a weaker version of PeterFalvi (3.8). *)
Lemma cycTI_NC_minn (phi : 'CF(G)) : 
    {in V, forall x, phi x = 0} -> (0 < NC phi < 2 * minn w1 w2)%N ->
  (minn w1 w2 <= NC phi)%N.
Proof.
rewrite card_gt0 => ZphiV /andP[/set0Pn[[i1 j1]]]; rewrite inE /= => NZs NN.
pose a i j := '[phi, sigma (w_ i j)]; pose S := [set ij | a ij.1 ij.2 != 0].
pose L := [set (i1, j) | j : Iirr W2]; pose C := [set (i, j1) | i : Iirr W1].
have cL : #|L| = w2 by rewrite card_imset // => i j [].
have cC : #|C| = w1 by rewrite card_imset // => i j [].
have [Da | Da] := small_cycTI_NC ZphiV NN NZs.
  suff /subset_leq_card: C \subset S by apply: leq_trans; rewrite cC geq_minl.
  by apply/subsetP=> _ /imsetP[i2 _ ->]; rewrite !inE /= /a Da eqxx mul1r.
suff /subset_leq_card: L \subset S by apply: leq_trans; rewrite cL geq_minr.
by apply/subsetP=> _ /imsetP[j2 _ ->]; rewrite !inE /= /a Da eqxx mul1r.
Qed.

(* Another consequence of (3.8), used in (4.8), (10.5), (10.10) and (11.8). *)
Lemma eq_signed_sub_cTIiso phi e i j1 j2 :
    let rho := (-1) ^+ e *: (eta_ i j1 - eta_ i j2) in
    phi \in 'Z[irr G] -> '[phi] = 2%:R -> j1 != j2 ->
  {in V, phi =1 rho} -> phi = rho.
Proof.
set rho := _ - _; move: phi => phi0 /= Zphi0 n2phi0 neq_j12 eq_phi_rho.
pose phi := (-1) ^+ e *: phi0; pose psi := phi - rho.
have{eq_phi_rho} psiV0 z: z \in V -> psi z = 0.
  by move=> Vz; rewrite !cfunE eq_phi_rho // !cfunE signrMK subrr.
have{Zphi0} Zphi: phi \in 'Z[irr G] by rewrite rpredZsign.
have{n2phi0} n2phi: '[phi] = 2%:R by rewrite cfnorm_sign.
have Zrho: rho \in 'Z[irr G] by rewrite rpredB ?cycTIiso_vchar.
have n2rho: '[rho] = 2%:R.
  by rewrite cfnormBd !cfdot_cycTIiso ?eqxx ?(negPf neq_j12) ?andbF.
have [oIphi _ Dphi] := dirr_small_norm Zphi n2phi isT.
have [oIrho _ Drho] := dirr_small_norm Zrho n2rho isT.
set Iphi := dirr_constt _ in oIphi Dphi.
set Irho := dirr_constt _ in oIrho Drho.
suffices /eqP eqIrho: Irho == Iphi by rewrite Drho eqIrho -Dphi signrZK.
have psi_phi'_lt0 di: di \in Irho :\: Iphi -> '[psi, dchi di] < 0.
  case/setDP=> rho_di phi'di; rewrite cfdotBl subr_lt0.
  move: rho_di; rewrite dirr_consttE; apply: ler_lt_trans.
  rewrite real_lerNgt -?dirr_consttE ?real0 ?Creal_Cint //.
  by rewrite Cint_cfdot_vchar ?dchi_vchar.
have NCpsi: (NC psi < 2 * minn w1 w2)%N.
  suffices NCpsi4: (NC psi <= 2 + 2)%N.
    by rewrite (leq_ltn_trans NCpsi4) // !addnn mul2n ltn_double leq_min w1gt2.
  by rewrite cycTI_NC_sub // cycTI_NC_norm ?n2phi ?n2rho.
pose rhoId := dirr_dIirr (fun sk => (-1) ^+ (sk.1 : bool) *: eta_ i sk.2).
have rhoIdE s k: dchi (rhoId (s, k)) = (-1) ^+ s *: eta_ i k.
  by apply: dirr_dIirrE => sk; rewrite rpredZsign cycTIiso_dirr.
rewrite eqEcard oIrho oIphi andbT -setD_eq0; apply/set0Pn=> [[dk1 phi'dk1]].
have [[rho_dk1 _] psi_k1_lt0] := (setDP phi'dk1, psi_phi'_lt0 _ phi'dk1).
have dot_dk1: '[rho, dchi dk1] = 1.
  rewrite Drho cfdot_suml (big_setD1 dk1) //= cfnorm_dchi big1 ?addr0 //.
  move=> dk2 /setD1P[/negPf dk1'2 /dirr_constt_oppl]; rewrite cfdot_dchi dk1'2.
  by case: eqP => [-> /negP[] | _ _]; rewrite ?subrr ?ndirrK.
have dot_dk2: 0 < '[rho, rho - dchi dk1].
  by rewrite cfdotBr dot_dk1 n2rho addrK ltr01.
have{dot_dk1 dot_dk2} [s [k Dk1 rho_k2]]:
  exists s, exists2 k, rhoId (s, k.1) = dk1 & rhoId (~~ s, k.2) \in Irho.
- move/cfdot_add_dirr_eq1: dot_dk1.
  rewrite dirr_dchi rpredN !cycTIiso_dirr //.
  case=> // Dk1; [exists false, (j1, j2) | exists true, (j2, j1)];
    try apply: dirr_inj; rewrite ?dirr_consttE rhoIdE scaler_sign //=.
  + by rewrite addrC Dk1 addKr in dot_dk2.
  by rewrite Dk1 addrK in dot_dk2.
rewrite -Dk1 rhoIdE cfdotZr rmorph_sign in psi_k1_lt0.
have psi_k1_neq0: '[psi, eta_ i k.1] != 0.
  by rewrite -(can_eq (signrMK s)) mulr0 ltr_eqF.
set dk2 := rhoId _ in rho_k2.
have NCk2'_le1 (dI : {set _}):
  dk2 \in dI -> #|dI| = 2%N -> (NC (\sum_(dk in dI :\ dk2) dchi dk)%R <= 1)%N.
- rewrite (cardsD1 dk2) => -> /eqP/cards1P[dk ->].
  by rewrite big_set1 cycTI_NC_dirr ?dirr_dchi.
suffices /psi_phi'_lt0/ltr_geF/idP[]: dk2 \in Irho :\: Iphi.
  rewrite rhoIdE cfdotZr signrN rmorphN mulNr oppr_ge0 rmorph_sign.  
  have := small_cycTI_NC psiV0 NCpsi psi_k1_neq0.
  by case=> // ->; rewrite mulrCA nmulr_lle0 ?ler0n.
have: (1 + 1 < NC psi)%N.
  apply (@leq_trans (minn w1 w2)); first by rewrite leq_min w1gt2.
  apply: cycTI_NC_minn => //; rewrite NCpsi /NC.
  by rewrite (cardsD1 (i, k.1)) inE /= psi_k1_neq0.
rewrite inE rho_k2 andbT ltnNge; apply: contra => phi_k2.
rewrite /psi Drho (big_setD1 dk2) //= Dphi (big_setD1 dk2) //=.
by rewrite addrAC opprD addNKr addrC cycTI_NC_sub ?NCk2'_le1.
Qed.

(* This is PeterFalvi (3.9)(a). *)
Lemma eq_in_cycTIiso (i : Iirr W) (phi : 'CF(G)) :
  phi \in dirr G -> {in V, phi =1 'chi_i} -> phi = sigma 'chi_i.
Proof.
move=> Dphi; rewrite -(inv_dprod_IirrK defW i).
case: (inv_dprod_Iirr _)=> /= i1 j1 EphiC.
pose psi : 'CF(G) := eta_ i1 j1 - phi.
have ZpsiV: {in V, forall g, psi g = 0}=> [g GiV|].
  by rewrite /psi !cfunE cycTIiso_restrict // -(EphiC _ GiV) subrr.
pose a i j := '[psi, eta_ i j]; pose S := [set ij | a ij.1 ij.2 != 0].
case: (boolP ((i1, j1) \in S))=> [I1J1iS|]; last first.
  rewrite inE negbK /a  cfdotBl cfdot_cycTIiso !eqxx /=.
  rewrite cfdot_dirr ?(mem_dirr, cycTIiso_dirr) //.
  case: (boolP (phi == _))=> [|_].
    by rewrite opprK -(natrD _ 1 1) pnatr_eq0.
  case: (boolP (phi == _))=> [/eqP //|].
  by rewrite subr0 oner_eq0.
have SPos : (0 < #|S|)%N by rewrite (cardD1 (i1,j1)) I1J1iS.
have SLt: (#|S| <= 2)%N.
  by rewrite -[2]add1n cycTI_NC_sub // !cycTI_NC_dirr // cycTIiso_dirr.
have: (0 < #|S| < 2 * minn w1 w2)%N.
  rewrite SPos; apply: leq_ltn_trans SLt _.
  by rewrite -{1}[2%N]muln1 ltn_mul2l /= leq_min ![(1 < _)%N]ltnW.
move/(cycTI_NC_minn ZpsiV); rewrite leqNgt; case/negP.
by apply: leq_ltn_trans SLt _; rewrite leq_min w1gt2.
Qed.

(* This is the second part of Peterfalvi (3.9a). *)
Lemma cfAut_cycTIiso u phi : cfAut u (sigma phi) = sigma (cfAut u phi).
Proof.
rewrite [phi]cfun_sum_cfdot !raddf_sum; apply: eq_bigr => ij _.
rewrite /= !(linearZ, cfAutZ) /= -aut_IirrE; congr (_ *: _) => {phi}.
apply: eq_in_cycTIiso => [|x Vx /=].
  by have /cycTIirrP[i [j ->]] := mem_irr ij; rewrite dirr_aut cycTIiso_dirr.
by rewrite cfunE cycTIiso_restrict // aut_IirrE cfunE.
Qed.

Section AutCyclicTI.

Variable iw : Iirr W.
Let w := 'chi_iw.
Let a := #[w]%CF.

Let Zsigw : sigma w \in 'Z[irr G].
Proof. by have [_ -> //] := cycTI_Zisometry; apply: irr_vchar. Qed.

Let lin_w: w \is a linear_char := Wlin iw.

(* This is Peterfalvi (3.9)(b). *)
Lemma cycTIiso_aut_exists k :
    coprime k a ->
  [/\ exists u, sigma (w ^+ k) = cfAut u (sigma w)
    & forall x, coprime #[x] a -> sigma (w ^+ k) x = sigma w x].
Proof.
case/(make_pi_cfAut G)=> u Du_a Du_a'.
suffices Dwk: sigma (w ^+ k) = cfAut u (sigma w).
  by split=> [|x co_x_a]; [exists u | rewrite Dwk Du_a'].
rewrite cfAut_cycTIiso; congr (sigma _); apply/cfun_inP=> x Wx.
have Wxbar: coset _ x \in (W / cfker w)%G by rewrite mem_quotient.
rewrite exp_cfunE // cfunE -cfQuoEker //.
rewrite -lin_charX ?cfQuo_lin_char ?cfker_normal // -Du_a ?cfunE //.
  by rewrite char_vchar ?cfQuo_char ?irr_char.
by rewrite [a]cforder_lin_char // dvdn_exponent.
Qed.

(* This is Peterfalvi (3.9)(c). *)
Lemma Cint_cycTIiso_coprime x : coprime #[x] a -> sigma w x \in Cint.
Proof.
move=> co_x_a; apply: Cint_rat_Aint (Aint_vchar _ Zsigw).
have [Qb galQb [QbC AutQbC [w_b genQb memQb]]] := group_num_field_exists <[x]>.
have{memQb} [wx Dwx]: exists wx, sigma w x = QbC wx.
  have /memQb Qbx := dvdnn #[x].
  have [sw1 /Qbx[wx1 Dwx1] [sw2 /Qbx[wx2 Dwx2] ->]] := vcharP _ Zsigw.
  by exists (wx1 - wx2); rewrite rmorphB !cfunE Dwx1 Dwx2.
suffices: wx \in fixedField 'Gal({:Qb} / 1).
  rewrite Dwx (galois_fixedField _ _ galQb) ?subvf // => /vlineP[z ->].
  by rewrite -in_algE fmorph_eq_rat fmorph_rat Crat_rat.
apply/fixedFieldP; split=> [|v_b _]; first exact: memvf.
have [v Dv] := AutQbC v_b; apply: (fmorph_inj QbC); rewrite Dv -Dwx.
have [u uQb uQb'] := dvd_restrict_cfAut (W / cfker w) #[x] v.
transitivity (sigma (cfAut u w) x); first by rewrite -cfAut_cycTIiso cfunE -uQb.
congr (sigma _ _); apply/cfun_inP=> y Wy; rewrite cfunE -cfQuoEker //.
rewrite uQb' ?char_vchar ?cfQuo_char ?irr_char // coprime_sym.
apply: coprime_dvdr co_x_a; rewrite [a]cforder_lin_char //.
by rewrite dvdn_exponent ?mem_quotient.
Qed.

End AutCyclicTI.

End Proofs.

Implicit Arguments ortho_cycTIiso_vanish [gT G W W1 W2 defW psi].

Lemma cycTIisoC (gT : finGroupType) (G W W1 W2 : {group gT})  
                (defW12 : W1 \x W2 = W) (ctiW12 : cyclicTI_hypothesis G defW12)
                (defW21 : W2 \x W1 = W) (ctiW21 : cyclicTI_hypothesis G defW21)
                i j :
   cyclicTIiso ctiW12 (cyclicTIirr defW12 i j)
     = cyclicTIiso ctiW21 (cyclicTIirr defW21 j i).
Proof.
rewrite (cyclicTIirrC  _ defW21); move: (cyclicTIirr _ i j) => w.
by rewrite /cyclicTIiso !unlock_with /cyclicTIiso_def /cyclicTIset setUC.
Qed.
