(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup ssrnum.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter frobenius PFsection1 PFsection2.

(******************************************************************************)
(* This file covers Peterfalvi, Section 3: TI-Subsets with Cyclic Normalizers *)
(******************************************************************************)
(* Defined here:                                                              *)
(*   cylicTIhypothesis G W W1 W2 == W1 \x W2 = W is a cyclic subgroup of G,   *)
(*                           W1 and W2 are nontrivial of coprime order, and   *)
(*                           W :\: (W1 :|: W2) is a non-empty TI subset of G. *)
(*                           This is Peterfalvi (3.1).                        *)
(* For ccW : cylicTIhypothesis G W W1 W2 we set                               *)
(*        cyclicTIset ccW == W :\: (W1 :|: W2).                               *)
(*      cyclicTIhyp_W1xW2 == W1 \x W2 = W.                                    *)
(*        cyclicTIirr i j == 'chi_(i * j) with i in Iirr W1 and j in Iirr W2  *)
(*            acTIirr i j ==  1 - w_ i 0 - w_ 0 j + w_ i j.                   *)
(*                            where w_ i j = cyclicTIirr i j.                 *)
(*            bcTIirr i j == 'Ind[G] (alpha_ i j) - 1                         *)
(*                            where alpha_ i j = bcTIirr i j.                 *)
(*           dcTIirr i j  == a signed irreducible character of G such that    *)
(*                              beta_ i j = - x_ i 0 - x_ 0 j + x_ i j        *)
(*                            where beta_ i j = bcTIirr i j                   *)
(*                                     x_ i j = 'chi_(dcTIirr i j).           *)
(*          cyclicTIsigma == a linear isometry that extends induction from W  *)
(*                           to G.                                            *)
(*         cyclicTI_NC phi == the set of all pairs i j such that              *)
(*                            '[phi, sigma (w_ i j] != 0]|                    *)
(*                            where  w_ i j = cyclicTIirr i j                 *)
(*                                  sigma f = cyclicTIsigma f.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Definitions.

Variables (gT : finGroupType) (G W W1 W2 : {set gT}).

Definition cyclicTIhypothesis :=
  [/\ [/\ W1 \x W2 = W, cyclic W, odd #|W| & W \subset G],
      [/\ W1 != 1 & W2 != 1]
    & normedTI (W :\: (W1 :|: W2)) G W]%g.

Definition cyclicTIset of cyclicTIhypothesis := W :\: (W1 :|: W2).

End Definitions.
Section Proofs.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).

Hypothesis tiW : cyclicTIhypothesis G W W1 W2.

Lemma cyclicTIhyp_sym : cyclicTIhypothesis G W W2 W1.
Proof. by case: tiW; rewrite dprodC setUC => ? []. Qed.

Let w1 := #|W1|.
Let w2 := #|W2|.
Let V := cyclicTIset tiW.

Definition cyclicTIhyp_W1xW2 : W1 \x W2 = W. 
Proof. by have [[]] := tiW. Defined.

Local Notation W1xW2 := cyclicTIhyp_W1xW2.
Let sW1W : W1 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP W1xW2. Qed.
Let sW2W : W2 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP W1xW2. Qed.

Let cyclicW : cyclic W. Proof. by have [[]] := tiW. Qed.
Let cyclicW1 : cyclic W1. Proof. exact: cyclicS cyclicW. Qed.
Let cyclicW2 : cyclic W2. Proof. exact: cyclicS cyclicW. Qed.

Let oddW : odd #|W|. Proof. by have [[]] := tiW. Qed.
Let oddW1 : odd w1. Proof. exact: oddSg oddW. Qed.
Let oddW2 : odd w2. Proof. exact: oddSg oddW. Qed.

Let odd_neq2 m : odd m -> (2 == m)%N = false. Proof. by case: eqP => // <-. Qed.
Let tLW1 : (2 < w1)%N.
Proof. by rewrite ltn_neqAle cardG_gt1 odd_neq2 //; have [_ []] := tiW. Qed.
Let tLW2 : (2 < w2)%N.
Proof. by rewrite ltn_neqAle cardG_gt1 odd_neq2 //; have [_ []] := tiW. Qed.

Lemma cyclicTI_coprime : coprime #|W1| #|W2|.
Proof. by rewrite -(cyclic_dprod W1xW2). Qed.

Definition cyclicTIirr (i : Iirr W1) (j : Iirr W2) :=
 'chi_(odflt 0 [pick k |
       forallb g1 : gT, (g1 \in W1) ==> forallb g2 : gT, 
          (g2 \in W2) ==> 
                 ('chi[W]_k (g1 * g2)%g == 'chi_i g1 * 'chi_j g2)]).
Local Notation w_ := cyclicTIirr.

Lemma cTIirrE i j : w_ i j = 'chi_(dprod_Iirr W1xW2 (i, j)).
Proof.
rewrite /w_; case: pickP=> [k /forall_inP Hf |] /=.
  apply/cfunP=> g; case: (boolP (g \in W))=> [|GniW]; last by rewrite !cfun0.
  case/dprodP: W1xW2=> _ {1}<- _ _ /imset2P [g1 g2 G1iW1 G2iW2 ->].
  move/forall_inP: (Hf _ G1iW1)=> /(_ _ G2iW2) /eqP ->.
  by rewrite dprod_IirrE cfDprodE.
move/(_ (dprod_Iirr W1xW2 (i, j)))=> /idP [].
apply/forall_inP=> g1 G1iW1; apply/forall_inP=> g2 G2iW2.
by rewrite dprod_IirrE cfDprodE.
Qed.

Lemma cTIirr00 : w_ 0 0 = 1.
Proof.
rewrite cTIirrE dprod_IirrE !chi0_1.
apply/cfun_inP=> x Wx; rewrite cfun1E Wx.
case/(mem_dprod W1xW2): Wx => y [z [W1y W2z -> _]].
by rewrite cfDprodE // !cfun1E W1y W2z mulr1.
Qed.

Lemma cTIirr_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof. by rewrite !cTIirrE !dprod_IirrE !chi0_1 cfDprod1r cfDprod1l. Qed.

Lemma cTIirr_linearW i : lin_char ('chi[W]_i).
Proof.
by apply/char_abelianP; apply: cyclic_abelian; case: tiW; case.
Qed.

Lemma cTIirr_linearW1 i : lin_char ('chi[W1]_i).
Proof.
by apply/char_abelianP; apply: cyclic_abelian; case: tiW; case.
Qed.

Lemma cTIirr_linearW2 i : lin_char ('chi[W2]_i).
Proof.
by apply/char_abelianP; apply: cyclic_abelian; case: tiW; case.
Qed.

Let classesW1 : #|classes W1| = w1.
Proof.
by have:= cyclic_abelian cyclicW1; rewrite card_classes_abelian => /eqP ->.
Qed.

Let classesW2 : #|classes W2| = w2.
Proof.
by have:= cyclic_abelian cyclicW2; rewrite card_classes_abelian => /eqP ->.
Qed.

Definition acTIirr i j : 'CF(W) := (1 - w_ i 0) * (1 - w_ 0 j).
Local Notation alpha_ := acTIirr.

Lemma acTIirr1 i j : alpha_ i j 1%g = 0.
Proof.
rewrite !cfunE /cyclicTIirr cfun1Egen group1 (lin_char1 ( cTIirr_linearW _)).
by rewrite addrN mul0r.
Qed.

Lemma acTIirrE i j : alpha_ i j = 1 - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite /alpha_ mulrBl mul1r mulrBr mulr1 -cTIirr_split.
by rewrite opprB !addrA addrAC (addrAC 1).
Qed.

Lemma acTIirr_vchar i j : alpha_ i j \in 'Z[irr W].
Proof. by rewrite mul_vchar // -chi0_1 sub_zchar ?irr_vchar. Qed.

Lemma memc_acTIirr i j : alpha_ i j \in 'CF(W, V).
Proof.
apply/cfun_onP=> x; rewrite !inE negb_and negbK orbC.
have [Wx /= | /cfun0->//] := boolP (x \in W).
rewrite !cfunE cfun1E Wx !cTIirrE !dprod_IirrE !chi0_1 cfDprod1l cfDprod1r.
have LW1 := cTIirr_linearW1; have LW2 := cTIirr_linearW2.
rewrite -{3}[x]mul1g -{4}[x]mulg1; case/orP=> [W1x | W2x]; last first.
  by rewrite cfDprodEl // lin_char1 ?(subrr, mul0r).
by rewrite mulrC cfDprodEr // lin_char1 ?(subrr, mul0r).
Qed.

Definition bcTIirr i j : 'CF(G) := 'Ind[G] (alpha_ i j) - 1.

Local Notation beta_ := bcTIirr.

Lemma bcTIirr_vchar i j : beta_ i j \in 'Z[irr G].
Proof. 
by rewrite sub_zchar ?cfInd_vchar ?acTIirr_vchar // -chi0_1 irr_vchar. 
Qed.

Lemma cfdot_cTIirr i j i' j' :
  '[w_ i j, w_ i' j'] = ((i == i') && (j == j'))%:R.
Proof. rewrite !cTIirrE cfdot_irr inj_eq //; exact: dprod_Iirr_inj. Qed.

Lemma cfdot_acTIirr i j i' j' : i' != 0 -> j' != 0 ->
  '[alpha_ i j, w_ i' j'] = ((i == i') && (j == j'))%:R.
Proof.
move=> /negbTE Di' /negbTE Dj'; rewrite acTIirrE -cTIirr00 cfdotDl !cfdot_subl.
by rewrite !cfdot_cTIirr !(eq_sym 0) Di' Dj' !andbF !subr0 add0r.
Qed.

Lemma cfdot_acTIirr00 i j : i != 0 -> j != 0 -> '[alpha_ i j, 1] = 1.
Proof.
move=> /negbTE Di /negbTE Dj; rewrite acTIirrE -cTIirr00 cfdotDl !cfdot_subl.
by rewrite !cfdot_cTIirr Di Dj !subr0 addr0.
Qed.

Lemma cfnorm_acTIirr i j : i != 0 -> j != 0 -> '[alpha_ i j] = 4%:R.
Proof.
move=> Di Dj; rewrite {2}acTIirrE cfdotDr !cfdot_subr cfdot_acTIirr00 // addrC.
rewrite cfdot_acTIirr // !addrA -mulrSr.
rewrite acTIirrE -cTIirr00  !(cfdot_subl, cfdotDl) !cfdot_cTIirr.
rewrite !eqxx !(eq_sym 0) (negbTE Di) (negbTE Dj) !andbF !subr0 !addr0.
by rewrite !add0r !opprK -!mulrSr.
Qed.

Lemma cfdot_Ind_acTIirr_1 i j : i != 0 -> j != 0 -> 
  '['Ind[G] (alpha_ i j), 1] = 1.
Proof.
move=> Di Dj; have WsG : W \subset G by case: tiW; case.
by rewrite -Frobenius_reciprocity cfRes_cfun1 // cfdot_acTIirr00.
Qed.

Let VsG : V \subset G^#.
Proof.
apply/subsetP=> g; rewrite !inE negb_or -andbA; case/and3P=> [GniW1 GniW2 GiW].
have WsG : W \subset G by case: tiW; case.
rewrite (subsetP WsG) // andbT; apply: contra GniW1; move/eqP->.
by exact: group1.
Qed.

(* This is the first equation of Peterfalvi (3.5.1). *)
Lemma cfdot_bcTIirr_1 i j : i != 0 -> j != 0 -> '[beta_ i j, 1] = 0.
Proof.
move=> Di Dj.
by rewrite cfdot_subl cfdot_Ind_acTIirr_1 // -chi0_1 cfdot_irr subrr.
Qed.

(* These are the other equations of Peterfalvi (3.5.1). *)
Lemma cfdot_bcTIirr i j i' j' : i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> 
  '[beta_ i j, beta_ i' j'] =
     ((i == i') * (j == j') + (i == i') + (j == j'))%:R.
Proof.
move=> Di Dj Di' Dj'. 
rewrite cfdot_subr cfdot_bcTIirr_1 // subr0.
rewrite cfdot_subl (cfdotC 1) cfdot_Ind_acTIirr_1 // rmorph1.
have nTi: normedTI (W :\: (W1 :|: W2)) G W by case: tiW.
rewrite (normedTI_isometry _ nTi) ?memc_acTIirr //.
rewrite (acTIirrE i') cfdotDr !cfdot_subr cfdot_acTIirr00 //.
rewrite addrC -!addrA addKr acTIirrE -cTIirr00 !(cfdot_subl, cfdotDl).
rewrite !cfdot_cTIirr !eqxx !(eq_sym 0) !andbT.
do !rewrite (@negbTE (_ == 0)) ?andbF //; rewrite !opprD !oppr0 !opprK.
by rewrite !add0r !addr0 mulnb addrA addrC addrA -!natrD.
Qed.

Lemma cfnorm_bcTIirr i j : i != 0 -> j != 0 -> '[beta_ i j] = 3%:R.
Proof.
by move=> NZi1 NZj1; rewrite (cfdot_bcTIirr NZi1 NZj1 NZi1 NZj1) !eqxx.
Qed.

Lemma dim_cyclicTIcfun : \dim 'CF(W, V) = (#|Iirr W1|.-1 * #|Iirr W2|.-1)%N.
Proof.
rewrite !card_ord dim_cfun_on_abelian ?(cyclic_abelian, subsetDl) // !NirrE.
have:= cyclic_abelian cyclicW1; rewrite card_classes_abelian => /eqP ->.
have:= cyclic_abelian cyclicW2; rewrite card_classes_abelian => /eqP ->.
apply: (@addnI (w1 + w2)%N); rewrite -{1}cardsUI addnAC.
have [_ defW _ ->] := dprodP W1xW2; rewrite cards1.
have /setIidPr <-: (W1 :|: W2) \subset W by rewrite subUset -mulG_subG defW.
rewrite cardsID -(dprod_card W1xW2) /w1 -(prednK (cardG_gt0 W1)) /= -/w1 -/w2.
by rewrite addn1 !addSn addnAC -mulnS mulSnr prednK ?cardG_gt0.
Qed.

Definition acTIirr_base :=
  image (prod_curry alpha_) (setX [set~ ord0] [set~ ord0]).

Lemma acTIirr_base_free : free acTIirr_base.
Proof.
apply/freeP=> s s_alpha_0 ij; case def_ij: (enum_val ij) => [i j].
have /andP[Di Dj]: (i != 0) && (j != 0).
  by rewrite -!in_setC1 -in_setX -def_ij enum_valP.
have:= congr1 (cfdotr (w_ i j)) s_alpha_0; rewrite raddf_sum raddf0 => <-.
rewrite (bigD1 ij) //= -tnth_nth tnth_map /tnth -enum_val_nth def_ij.
rewrite cfdotZl cfdot_acTIirr // !eqxx mulr1 big1 ?addr0 // => kl.
rewrite -tnth_nth tnth_map /tnth -enum_val_nth -(inj_eq enum_val_inj).
case: (enum_val kl) => k l /= => /negbTE ne_kl_ij.
by rewrite cfdotZl cfdot_acTIirr // -xpair_eqE -def_ij ne_kl_ij mulr0.
Qed.

(* This is Peterfalvi (3.4). *)
Lemma acTIirr_base_basis : basis_of 'CF(W,V) acTIirr_base.
Proof.
rewrite /basis_of acTIirr_base_free andbT -dimv_leqif_eq.
  rewrite (eqnP acTIirr_base_free) size_tuple cardsX !cardsC1.
  by rewrite dim_cyclicTIcfun.
by apply/span_subvP=> _ /imageP[[i j] _ ->]; apply: memc_acTIirr.
Qed.

Lemma card_dirr_const_beta_diff i j i' j' :
  i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> i != i' -> j != j' -> 
  #|dirr_constt (beta_ i j) :&: dirr_constt (beta_ i' j')| = 
  #|dirr_constt (beta_ i j) :&: dirr_constt (-beta_ i' j')|.
Proof.
move=> NZi NZj NZi' NZj' IdI' JdJ'.
apply/eqP; rewrite -eqC_nat -subr_eq0; apply/eqP; rewrite -cfdot_sum_dchi.
pose F i j N1 N2 := dirr_small_norm (bcTIirr_vchar i j) (cfnorm_bcTIirr N1 N2).
case: (F _ _ NZi NZj)=> // _ _ <-; case: (F _ _ NZi' NZj')=> // _ _ <-.
by rewrite cfdot_bcTIirr // (negPf IdI') (negPf JdJ').
Qed.

Lemma card_dirr_const_beta_diffr i j j' :
  i != 0 -> j != 0 -> j' != 0 -> j != j' -> 
  #|dirr_constt (beta_ i j) :&: dirr_constt (beta_ i j')| = 1%N /\
  #|dirr_constt (beta_ i j) :&: dirr_constt (-beta_ i j')| = 0%N.
Proof.
move=> NZi NZj NZj' JdJ'.
have : '[beta_ i j, beta_ i j'] = 1.
  by rewrite (cfdot_bcTIirr NZi NZj NZi NZj') !eqxx (negPf JdJ').
pose DS i j N1 N2 :=
  dirr_small_norm (bcTIirr_vchar i j) (cfnorm_bcTIirr N1 N2).
case: (DS _ _ NZi NZj)=> // Acard IA AS.
case: (DS _ _ NZi NZj')=> // Bcard IB BS.
rewrite {1}AS {1}BS cfdot_sum_dchi => /eqP.
rewrite subr_eq -(natrD _ 1%N) eqr_nat.
set A := dirr_constt _; set B := dirr_constt _; set C := dirr_constt _.
set A1 := _ :&: _; case: (set_0Vmem A1)=> [-> //| [u1 U1iA1]].
  by rewrite cards0.
rewrite [#|A1|](cardsD1 u1) ?U1iA1.
move: U1iA1; rewrite inE => /andP [U1iA U1iB].
set A2 := _ :\ _; case: (set_0Vmem A2)=> [-> //| [u2 U2iA2]].
  by rewrite cards0 addn0; case: #|_|.
rewrite [#|A2|](cardsD1 u2) ?U2iA2.
move: U2iA2; rewrite 3!inE => /and3P [U2dU1 U2iA U2iB].
set A3 := _ :\ _; case: (set_0Vmem A3)=> [-> //| [u3]]; last first.
  rewrite 5!inE => /and4P [U3dU2 U3dU1 U3iA U3iB].
  set A4 := _ :&: _; case: (set_0Vmem A4)=> [->| [u4]].
    by rewrite cards0.
  rewrite inE => /andP [U4iA U4iC].
  move: Acard; rewrite -/A (cardsD1 u1) U1iA (cardsD1 u2) 2!inE U2iA U2dU1 /=.
  rewrite (cardsD1 u3) 4!inE U3iA U3dU2 U3dU1.
  rewrite {1}(cardsD1 u4) 6!inE U4iA.
  case: (boolP (_ == _))=> [/eqP U4eU3 | _].
    case/negP: (dirr_constt_oppl U4iC).
    by rewrite -dirr_constt_oppr opprK U4eU3.
  case: (boolP (_ == _))=> [/eqP U4eU2 | _].
    case/negP: (dirr_constt_oppl U4iC).
    by rewrite -dirr_constt_oppr opprK U4eU2.
  case: (boolP (_ == _))=> [/eqP U4eU1 | //].
  case/negP: (dirr_constt_oppl U4iC).
  by rewrite -dirr_constt_oppr opprK U4eU1.
rewrite cards0 addn0.
set A4 := _ :&: _; case: (set_0Vmem A4)=> [-> //| [u3]].
  by rewrite cards0.
rewrite inE => /andP [U3iA U3iC].
rewrite [#|A4|](cardsD1 u3) inE U3iA U3iC /=.
have Abeta: beta_ i j = dchi u1 + dchi u2 + dchi u3.
  move: Acard; rewrite -/A AS -/A (cardsD1 u1) (bigD1 u1) ?U1iA //=.
  rewrite (cardsD1 u2) (bigD1 u2) ?(U2iA, U2dU1, inE) //=.
  have U3dU1 : u3 != u1.
    apply: contra (dirr_constt_oppl U1iB) => /eqP U3eU1.
    by rewrite -dirr_constt_oppr -U3eU1.
  have U3dU2 : u3 != u2.
    apply: contra (dirr_constt_oppl U2iB) => /eqP U3eU2.
    by rewrite -dirr_constt_oppr -U3eU2.
  rewrite (cardsD1 u3) (bigD1 u3) ?(U3iA, U3dU1, U3dU2, inE) //= => HH.
  rewrite big1 ?(addr0, addrA) // => u4; rewrite -!andbA.
  case/and4P => U4iA U4dU1 U4dU2 U4dU3; move: HH.
  by rewrite (cardsD1 u4) ?(U4iA, U4dU1, U4dU2, U4dU3, inE).
have Bbeta: beta_ i j' = dchi u1 + dchi u2 - dchi u3.
  move: Bcard; rewrite -/B BS -/B (cardsD1 u1) (bigD1 u1) ?U1iB //=.
  rewrite (cardsD1 u2) (bigD1 u2) ?(U2iB, U2dU1, inE) //=.
  have NU3dU1 : ndirr u3 != u1.
    by apply: contra (dirr_constt_oppl U3iA) => /eqP ->.
  have NU3dU2 : ndirr u3 != u2.
    by apply: contra (dirr_constt_oppl U3iA) => /eqP ->.
  have NU3iB : ndirr u3 \in B by rewrite -dirr_constt_oppr.
  rewrite (cardsD1 (ndirr u3)) (bigD1 (ndirr u3))
              ?(NU3iB, NU3dU1, NU3dU2, inE) //= => HH.
  rewrite dchi_ndirrE big1 ?(addr0, addrA) // => u4; rewrite -!andbA.
  case/and4P => U4iA U4dU1 U4dU2 U4dU3; move: HH.
  by rewrite (cardsD1 u4) ?(U4iA, U4dU1, U4dU2, U4dU3, inE).
have: (2%:R * dchi u3) 1%g = (beta_ i j - beta_ i j') 1%g.
  have->: 2%:R = 1 + 1 :> 'CF(G) by rewrite -(natrD _ 1 1).
  rewrite mulrDl !mul1r.
  rewrite Abeta Bbeta !opprD opprK -opprD [dchi u1 + _ + _]addrC.
  by rewrite addrA addrK.
rewrite /bcTIirr [X in _ - X]addrC opprD opprK addrA subrK.
rewrite -raddfB /= cfInd1 //; last by case: tiW; case.
rewrite 4!cfunE acTIirr1 cfunE acTIirr1 subr0 mulr0.
rewrite cfun1Egen group1 -natrD.
move/eqP; rewrite mulf_eq0 pnatr_eq0 orFb.
by rewrite mulr_sign; case: u3.1; rewrite ?oppr_eq0 (negPf (irr1_neq0 u3.2)).
Qed.

Lemma card_dirr_const_beta_diffl i i' j :
  i != 0 -> i' != 0 -> j != 0 -> i != i' -> 
  #|dirr_constt (beta_ i j) :&: dirr_constt (beta_ i' j)| = 1%N /\
  #|dirr_constt (beta_ i j) :&: dirr_constt (-beta_ i' j)| = 0%N.
Proof.
move=> NZi NZi' NZj IdI'.
have : '[beta_ i j, beta_ i' j] = 1.
  by rewrite (cfdot_bcTIirr NZi NZj NZi' NZj) !eqxx (negPf IdI').
pose DS i j N1 N2 :=
  dirr_small_norm (bcTIirr_vchar i j) (cfnorm_bcTIirr N1 N2).
case: (DS _ _ NZi NZj) => // Acard IA AS.
case: (DS _ _ NZi' NZj)=> // Bcard IB BS.
rewrite {1}AS {1}BS cfdot_sum_dchi => /eqP.
rewrite subr_eq -(natrD _ 1%N) eqr_nat.
set A := dirr_constt _; set B := dirr_constt _; set C := dirr_constt _.
set A1 := _ :&: _; case: (set_0Vmem A1)=> [-> //| [u1 U1iA1]].
  by rewrite cards0.
rewrite [#|A1|](cardsD1 u1) ?U1iA1.
move: U1iA1; rewrite inE => /andP [U1iA U1iB].
set A2 := _ :\ _; case: (set_0Vmem A2)=> [-> //| [u2 U2iA2]].
  by rewrite cards0 addn0; case: #|_|.
rewrite [#|A2|](cardsD1 u2) ?U2iA2.
move: U2iA2; rewrite 3!inE => /and3P [U2dU1 U2iA U2iB].
set A3 := _ :\ _; case: (set_0Vmem A3)=> [-> //| [u3]]; last first.
  rewrite 5!inE => /and4P [U3dU2 U3dU1 U3iA U3iB].
  set A4 := _ :&: _; case: (set_0Vmem A4)=> [->| [u4]].
    by rewrite cards0.
  rewrite inE => /andP [U4iA U4iC].
  move: Acard; rewrite -/A (cardsD1 u1) U1iA (cardsD1 u2) 2!inE U2iA U2dU1 /=.
  rewrite (cardsD1 u3) 4!inE U3iA U3dU2 U3dU1.
  rewrite {1}(cardsD1 u4) 6!inE U4iA.
  case: (boolP (_ == _))=> [/eqP U4eU3 | _].
    case/negP: (dirr_constt_oppl U4iC).
    by rewrite -dirr_constt_oppr opprK U4eU3.
  case: (boolP (_ == _))=> [/eqP U4eU2 | _].
    case/negP: (dirr_constt_oppl U4iC).
    by rewrite -dirr_constt_oppr opprK U4eU2.
  case: (boolP (_ == _))=> [/eqP U4eU1 | //].
  case/negP: (dirr_constt_oppl U4iC).
  by rewrite -dirr_constt_oppr opprK U4eU1.
rewrite cards0 addn0.
set A4 := _ :&: _; case: (set_0Vmem A4)=> [-> //| [u3]].
  by rewrite cards0.
rewrite inE => /andP [U3iA U3iC].
rewrite [#|A4|](cardsD1 u3) inE U3iA U3iC /=.
have Abeta: beta_ i j = dchi u1 + dchi u2 + dchi u3.
  move: Acard; rewrite -/A AS -/A (cardsD1 u1) (bigD1 u1) ?U1iA //=.
  rewrite (cardsD1 u2) (bigD1 u2) ?(U2iA, U2dU1, inE) //=.
  have U3dU1 : u3 != u1.
    apply: contra (dirr_constt_oppl U1iB) => /eqP U3eU1.
    by rewrite -dirr_constt_oppr -U3eU1.
  have U3dU2 : u3 != u2.
    apply: contra (dirr_constt_oppl U2iB) => /eqP U3eU2.
    by rewrite -dirr_constt_oppr -U3eU2.
  rewrite (cardsD1 u3) (bigD1 u3) ?(U3iA, U3dU1, U3dU2, inE) //= => HH.
  rewrite big1 ?(addr0, addrA) // => u4; rewrite -!andbA.
  case/and4P => U4iA U4dU1 U4dU2 U4dU3; move: HH.
  by rewrite (cardsD1 u4) ?(U4iA, U4dU1, U4dU2, U4dU3, inE).
have Bbeta: beta_ i' j = dchi u1 + dchi u2 - dchi u3.
  move: Bcard; rewrite -/B BS -/B (cardsD1 u1) (bigD1 u1) ?U1iB //=.
  rewrite (cardsD1 u2) (bigD1 u2) ?(U2iB, U2dU1, inE) //=.
  have NU3dU1 : ndirr u3 != u1.
    by apply: contra (dirr_constt_oppl U3iA) => /eqP ->.
  have NU3dU2 : ndirr u3 != u2.
    by apply: contra (dirr_constt_oppl U3iA) => /eqP ->.
  have NU3iB : ndirr u3 \in B by rewrite -dirr_constt_oppr.
  rewrite (cardsD1 (ndirr u3)) (bigD1 (ndirr u3))
              ?(NU3iB, NU3dU1, NU3dU2, inE) //= => HH.
  rewrite dchi_ndirrE big1 ?(addr0, addrA) // => u4; rewrite -!andbA.
  case/and4P => U4iA U4dU1 U4dU2 U4dU3; move: HH.
  by rewrite (cardsD1 u4) ?(U4iA, U4dU1, U4dU2, U4dU3, inE).
have: (2%:R * dchi u3) 1%g = (beta_ i j - beta_ i' j) 1%g.
  have->: 2%:R = 1 + 1 :> 'CF(G) by rewrite -(natrD _ 1 1).
  rewrite mulrDl !mul1r.
  rewrite Abeta Bbeta !opprD opprK -opprD [dchi u1 + _ + _]addrC.
  by rewrite addrA addrK.
rewrite /bcTIirr [X in _ - X]addrC opprD opprK addrA subrK.
rewrite -raddfB /= cfInd1 //; last by case: tiW; case.
rewrite 4!cfunE acTIirr1 cfunE acTIirr1 subr0 mulr0.
rewrite cfun1Egen group1 -natrD.
move/eqP; rewrite mulf_eq0 pnatr_eq0 orFb.
by rewrite mulr_sign; case: u3.1; rewrite ?oppr_eq0 (negPf (irr1_neq0 u3.2)).
Qed.

Lemma dirr_const_beta_inv i j v1 v2 v3 : i != 0 -> j != 0 ->
   beta_ i j = dchi v1 + dchi v2 + dchi v3 ->
   dirr_constt (beta_ i j) = [set v1; v2; v3].
Proof.
move=> NZi NZj BE.
case: (dirr_small_norm (bcTIirr_vchar i j) (cfnorm_bcTIirr NZi NZj)) => //.
move=> Acar _ betaE; apply/eqP; rewrite eqEcard; apply/andP; split; last first.
  by rewrite Acar !cardsU !cards1 (leq_trans (leq_subr _ _)) //
             addn1 ltnS leq_subr.
apply/subsetP=> v; rewrite !inE BE !cfdotDl !cfdot_dchi.
do 3 (case: (_ =P v)=> [<-| _]; first by rewrite eqxx ?orbT).
by rewrite !sub0r -!opprD -!natrD oppr_gt0 ltrn0.
Qed.

Section S3_5.

Section Main.

Variable W'1 W'2 : {group gT}.
Variable beta : Iirr W'1 -> Iirr W'2 -> 'CF(G).

Local Notation pA i j := (dirr_constt (beta i j)).
Local Notation nA i j := (dirr_constt (-beta i j)).
Local Notation dA i j v1 v2 v3 :=  
     [&& i != 0, j !=0 & pA i j == [set v1; v2; v3]].

Definition beta_hyp3_5 :=
  [/\ odd (Nirr W'1), odd (Nirr W'2),
      (2 < Nirr W'1)%N, (2 < Nirr W'2)%N &
      forall i j i' j',  i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> 
        [/\  #| pA i j | = 3, pA i j :&: nA i j = set0,
             i != i' -> j != j' ->  
               #|pA i j :&: pA i' j'| = #|pA i j :&: nA i' j'|,
             i != i' -> 
               #|pA i j :&: pA i' j| = 1%N /\ #|pA i j :&: nA i' j| = 0%N &
             j != j' -> 
               #|pA i j :&: pA i j'| = 1%N /\ #|pA i j :&: nA i j'| = 0%N]].

Hypothesis beta_hyp : beta_hyp3_5.

Let Oddw'1 := let (X,_,_,_,_) := beta_hyp in X.
Let Oddw'2 := let (_,X,_,_,_) := beta_hyp in X.
Let H2Lw'1 := let (_,_,X,_,_) := beta_hyp in X.
Let H2Lw'2 := let (_,_,_,X,_) := beta_hyp in X.
Let beta_diff := let (_,_,_,_,X) := beta_hyp in X.

Local Notation "v1 '<> v2" := ((v1 != v2) && (v1 != ndirr v2))%R (at level 10).

Lemma dAsl i j v1 v2 v3 : dA i j v1 v2 v3 -> dA i j v2 v1 v3.
Proof.
by case/and3P=> -> -> /eqP-> /=; rewrite eqEsubset; apply/andP;  
   split; apply/subsetP=> g; rewrite !inE -!orbA => /or3P []->; rewrite ?orbT.
Qed.

Lemma dAsr i j v1 v2 v3 : dA i j v1 v2 v3 -> dA i j v1 v3 v2.
Proof.
by case/and3P=> -> -> /eqP-> /=; rewrite eqEsubset; apply/andP;  
   split; apply/subsetP=> g; rewrite !inE -!orbA => /or3P []->; rewrite ?orbT.
Qed.

Lemma dAr i j v1 v2 v3 :  dA i j v1 v2 v3 ->  dA i j v3 v1 v2.
Proof. by move=> HH; apply: dAsl (dAsr _). Qed.

Lemma dAE i  j : i != 0 -> j != 0 -> {v | dA i j v.1.1 v.1.2 v.2}.
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

Lemma dA_in i j v1 v2 v3 : dA i j v1 v2 v3 -> v1 \in pA i j.
Proof. by case/and3P=> _ _ /eqP->; rewrite !inE eqxx. Qed.

Lemma dA_diff i j v1 v2 v3 : dA i j v1 v2 v3 -> v1 '<> v2.
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

Lemma dA_diffs i j v1 v2 v3 : 
 dA i j v1 v2 v3 -> [&& v1 '<> v2, v2 '<> v3 & v1 '<> v3].
Proof.
move=> HB; have HB1 := dAsr HB; have HB2 := dAsr (dAsl HB).
by rewrite !(dA_diff HB, dA_diff HB1, dA_diff HB2).
Qed.
 
Lemma dA_in_split i j v1 v2 v3 v : 
 dA i j v1 v2 v3 -> v \in pA i j -> [|| v == v1, v == v2 | v == v3].
Proof. by case/and3P=> _ _ /eqP->; rewrite !inE -!orbA. Qed.

Lemma dAEI i j k : i != 0 -> j != 0 -> k \in pA i j -> { v | dA i j k v.1 v.2}.
Proof.
move=> NZi NZj; case: (dAE NZi NZj)=> [[[v1 v2] v3]] /and3P [_ _ /eqP DAE].
rewrite {1}DAE !inE -orbA; case: (boolP (_ == _))=> [/eqP-> _|_].
  by exists (v2,v3); rewrite DAE NZi NZj /=.
case: (boolP (_ == _))=> [/eqP-> _|_].
  by exists (v1,v3); rewrite dAsl // DAE NZi NZj /=.
case: (boolP (_ == _))=> [/eqP-> _|//].
by exists (v1,v2); rewrite dAr // DAE NZi NZj /=.
Qed.

Lemma dA2r_diff i j k v1 v2 v3 v4 v5 : 
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

Lemma dA2l_diff i j k v1 v2 v3 v4 v5 :
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

Lemma dA2l_notin i1 i2 j v1 v2 v3 v4 v5 : 
   i1 != i2 -> dA i1 j v1 v2 v3 -> dA i2 j v1 v4 v5 -> v2 \notin pA i2 j.
Proof.
move=> I1dI2 Ai1j Ai2j; apply/negP.
move/(dA_in_split Ai2j)=> /or3P [] /eqP HH; 
    try (rewrite HH in Ai1j) ; try (rewrite HH in Ai2j).
- by move: (dA_diff Ai1j); rewrite eqxx.
- by move: (dA2l_diff I1dI2 Ai1j Ai2j); rewrite eqxx.
by move: (dA2l_diff I1dI2 Ai1j (dAsr Ai2j)); rewrite eqxx.
Qed.

Lemma dA2r_diffs  i j k v1 v2 v3 v4 v5 :
 j != k -> dA i j v1 v2 v3 -> dA i k v1 v4 v5 ->
 [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 & v3 '<> v5].
Proof.
move=> JdK HB HB'; have HB1 := dAsr HB; have HB1' := dAsr HB'.
by rewrite !(dA2r_diff _ HB HB', dA2r_diff _ HB HB1', dA2r_diff _ HB1 HB', 
             dA2r_diff _ HB1 HB1').
Qed.

Lemma dA2l_diffs  i j k v1 v2 v3 v4 v5 :
 j != k ->  dA j i v1 v2 v3 -> dA k i v1 v4 v5 ->
  [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 &  v3 '<> v5].
move=> JdK HB HB'; have HB1 := dAsr HB; have HB1' := dAsr HB'.
by rewrite !(dA2l_diff _ HB HB', dA2l_diff _ HB HB1', dA2l_diff _ HB1 HB', 
             dA2l_diff _ HB1 HB1').
Qed.

Lemma dAr_split i j k v1 v2 v3 :  k != 0 -> 
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

Lemma dAl_split i j k v1 v2 v3 :  k != 0 -> 
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

Lemma dA2_split i1 j1 i2 j2 v1 v2 v3 v4 v5 : i1 != i2 -> j1 != j2 -> 
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

Lemma dA2_n_split i1 j1 i2 j2 v1 v2 v3 v4 v5 : i1 != i2 -> j1 != j2 -> 
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

Lemma dAr_n_notin i j k v1 v2 v3 : j != 0 -> 
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

Lemma dAl_n_notin i j k v1 v2 v3 : j != 0 ->
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

Lemma dAr_n_notins i j k v1 v2 v3 : j != 0 -> dA i k v1 v2 v3 ->
 [&& ndirr v1 \notin pA i j, ndirr v2 \notin pA i j & ndirr v3 \notin pA i j].
Proof.
move=> NZj HB.
by rewrite !(dAr_n_notin _ HB, dAr_n_notin _ (dAsl HB), dAr_n_notin _ (dAr HB)).
Qed.

Lemma dAl_n_notins i j k v1 v2 v3 :  j != 0 -> dA k i v1 v2 v3 ->
 [&& ndirr v1 \notin pA j i, ndirr v2 \notin pA j i & ndirr v3 \notin pA j i].
Proof.
move=> NZj HB.
by rewrite !(dAl_n_notin _ HB, dAl_n_notin _ (dAsl HB), dAl_n_notin _ (dAr HB)).
Qed.

(* Technical lemma *)
Lemma main_aux i1 i2 i3 i4 j j' x1 x2 x3 x4 x5 x6 x7 :
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

(* This is almost PeterFalvi (3.5.5) *)
Lemma main : forall j, 
  {x | if (j == 0) then x = dirr1 _ else forall i, i != 0 -> x \in pA i j}.
Proof.
move=> j; case: (boolP (j == 0))=> [Zj | NZj]; first by exists (dirr1 _).
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
case: (boolP (forallb i , (i != 0) ==> (x1 \in pA i j))) => [/forallP HH|].
  by exists x1=> // i NZi; move/implyP: (HH i); move/(_ NZi).  
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
  (* This PF 3.5.4.6 *)
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
 (* This is 3.5.4.1 *)
have F1: x1 \in pA i1 j' -> dA i1 j' x1 (ndirr x5) (ndirr x7).
  by apply: main_aux Ai1j Ai2j Ai3j Ai4j.
have F2: x1 \in pA i2 j' -> dA i2 j' x1 (ndirr x3) (ndirr x7).
  by rewrite eq_sym in I2dI1; apply: main_aux Ai2j Ai1j (dAsl Ai3j) Ai4j.
have F3: x1 \in pA i4 j' -> dA i4 j' x1 (ndirr x3) (ndirr x5).
  by apply: main_aux Ai4j Ai1j (dAr Ai3j) Ai2j; rewrite // eq_sym.
 (* This is 3.5.4.2 *)
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
 (* This is 3.5.4.3 *)
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
 (* This is 3.5.4.4 *)
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
 (* This is 3.5.4.5 *)
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

Definition ccTIirr (i : Iirr W'2) := let (x, _) := main i in x.

Local Notation gamma_ := ccTIirr.

Lemma ccTIirrE i j : i != 0 -> j != 0 -> gamma_ j \in pA i j.
Proof.
move=> NZi NZj; rewrite /gamma_; case: (main j) => x.
by rewrite (negPf NZj)=> /(_ _ NZi).
Qed.

Lemma ccTIirr_inN i j j' : 
  i != 0 -> j != 0 -> j' != 0 -> j != j' ->  ndirr (gamma_ j') \notin pA i j.
Proof.
move=> NZi NZj NZj' JdJ'; apply/negP=> INg.
case: (dAEI NZi NZj' (ccTIirrE NZi NZj'))=> [[v1 v2 /=] Hv].
by case/andP: (dAr_n_notins NZj Hv)=> /negP.
Qed.

Lemma ccTIirr_inP i j j' : (4 < Nirr W'1)%N ->
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
    
End Main.

(* Horizontal instanciation *)
Fact h_beta_hyp : beta_hyp3_5 beta_.
Proof.
split; rewrite ?(NirrE, classesW1, classesW2) //=.
move=> i j i' j' NZi NZj NZi' NZj'.
have BE : '[beta_ i j] = 3%:R.
  by rewrite (cfdot_bcTIirr NZi NZj NZi NZj) !eqxx.
case: (dirr_small_norm (bcTIirr_vchar i j) BE)=> // HH HH1 _.
split=> //; first exact: card_dirr_const_beta_diff.
  by exact: card_dirr_const_beta_diffl.
by exact: card_dirr_const_beta_diffr.
Qed.

(* Vertical instanciation *)
Fact v_beta_hyp : beta_hyp3_5 (fun i => beta_^~ i).
Proof.
split; rewrite ?(NirrE, classesW1, classesW2) //=.
move=> i j i' j' NZi NZj NZi' NZj'.
have BE : '[beta_ j i] = 3%:R.
  by rewrite (cfdot_bcTIirr NZj NZi NZj NZi) !eqxx.
case: (dirr_small_norm (bcTIirr_vchar j i) BE)=> // HH HH1 _.
split=> //.
  by move=> H1 H2; apply: card_dirr_const_beta_diff.
  by move=> H1; apply: card_dirr_const_beta_diffr.
by move=> H1; apply: card_dirr_const_beta_diffl.
Qed.

Let Hcoprime : coprime w1 w2 := cyclicTI_coprime.
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
move: tLW1 tLW2 Hcoprime oddW1 oddW2.
rewrite leq_eqVlt; case/orP=> [/eqP {1}<- |].
  rewrite leq_eqVlt; case/orP=> [/eqP {1}<- //|].
  rewrite leq_eqVlt; case/orP=> [/eqP {2}<- //|].
  rewrite -{1}classesW2 -NirrE=> HW2 _ _ _.
  have [i' NZi' I'dI]: exists2 i', i' != 0 & i' != i.
    move: tLW1; rewrite -classesW1 -NirrE -[Nirr _]card_ord.
    rewrite (cardD1 (0: 'I__)) (cardD1 i) !inE NZi !ltnS=> /card_gt0P=> [[i1]].
    by rewrite !inE=> /and3P [] H1 H2 H3; exists i1.
  case/negP: (vcTIirr_inP HW2 NZj NZi' NZi I'dI).
  by rewrite HH hcTIirrE.
rewrite leq_eqVlt; case/orP=> [/eqP {2}<- //|].
rewrite -{1}classesW1 -NirrE=> HW1 _ _ _.
have [j' NZj' J'dJ]: exists2 j', j' != 0 & j' != j.
  move: tLW2; rewrite -classesW2 -NirrE -[Nirr _]card_ord.
  rewrite (cardD1 (0: 'I__)) (cardD1 j) !inE NZj !ltnS=> /card_gt0P=> [[j']].
  by rewrite !inE=> /and3P [] H1 H2 H3; exists j'.
case/negP: (hcTIirr_inP HW1 NZi NZj' NZj J'dJ).
by rewrite -HH vcTIirrE.
Qed.

Definition dcTIirr (i : Iirr W1) (j : Iirr W2) : dIirr G := 
  let v i := ndirr (vcTIirr i) in
  let h j := ndirr (hcTIirr j) in
  if (i == 0) then 
    if (j == 0) then dirr1 _ else h j
  else
    if (j == 0) then v i else
      dirr_dIirr (fun i => beta_ i j + dchi (h j) + dchi (v i)) i.

Local Notation x_ i j := (dchi (dcTIirr i j)).

Lemma dcTIrrE i j : i != 0 -> j != 0 -> beta_ i j = - x_ i 0 - x_ 0 j + x_ i j.
Proof.
move=> NZi NZj.
rewrite /dcTIirr !eqxx (negPf NZi) (negPf NZj).
pose TT := @dirr_dIirrPE _ _ _ _ (fun j => j != 0).
rewrite TT //; first by rewrite addrC !addrA !addrK.
move=> i1 NZi1.
case: (dirr_small_norm (bcTIirr_vchar i1 j) (cfnorm_bcTIirr NZi1 NZj)) => //.
move=> Acar _ ->; move/eqP: Acar; rewrite !dchi_ndirrE.
pose h := hcTIirr j; pose v := vcTIirr i1.
rewrite (cardsD1 h) (bigD1 h) /= hcTIirrE // [dchi _ + _]addrC addrK.
rewrite (cardsD1 v) (bigD1 v)  4?(hcTIirr_diff_vcTIrr, vcTIirrE, inE) //=.
rewrite [dchi _ + _]addrC addrK.
move/cards1P=> [hv Hhv].
rewrite (bigD1 hv) /= ?(big1, addr0, dirr_dchi) //.
  move=> v1; rewrite -!andbA => /and4P [V1iD V1dH V1dV /negP []].
  suff: v1 \in [set hv] by rewrite inE.
  by rewrite -Hhv 4!inE V1dH V1dV.
move/setP: Hhv=> /(_ hv); have->: hv \in [set hv] by rewrite inE.
by move/idP; rewrite 4!inE => /and3P [-> -> ->].
Qed.

Lemma dcTIrrDE i j : i != 0 -> j != 0 -> 
  dirr_constt (beta_ i j) = 
    [set ndirr (dcTIirr i 0); ndirr (dcTIirr 0 j); dcTIirr i j].
Proof.
move=> NZi NZj; apply: dirr_const_beta_inv=> //.
by rewrite !dchi_ndirrE -dcTIrrE.
Qed.

Lemma bcTIirr1 i j : i != 0 -> j != 0 -> 
  dirr1 _ \notin dirr_constt (beta_ i j).
Proof. by move=> NZi NZj; rewrite inE dchi1 cfdot_bcTIirr_1 ?ltrr. Qed.

Lemma bcTIirrM1 i j : i != 0 -> j != 0 -> 
  ndirr (dirr1 _) \notin dirr_constt (beta_ i j).
Proof.
move=> NZi NZj; rewrite inE dchi_ndirrE dchi1 cfdotNr cfdot_bcTIirr_1 //.
by rewrite oppr0 ltrr.
Qed.

Lemma dcTIirr_vchar i j : x_ i j \in 'Z[irr G].
Proof. by apply: dchi_vchar. Qed.

(* This is first part of Peterfalvi (3.5) *)
Lemma cfdot_dcTIirr i j i' j' : 
  '[x_ i j, x_ i' j'] = ((i == i') && (j == j'))%:R.
Proof.
move: i j i' j'.
pose i1 : Iirr W1 := inZp 1.
pose j1 : Iirr W2 := inZp 1.
have NZi1 : i1 != 0.
  apply/eqP; move/val_eqP=> /=.
  by rewrite modn_small // NirrE classesW1 (leq_trans _ tLW1).
have NZj1 : j1 != 0.
  apply/eqP; move/val_eqP=> /=.
  by rewrite modn_small // NirrE classesW2 (leq_trans _ tLW2).
have P0 : x_ 0 0 = 1 by rewrite {1}/dcTIirr !eqxx dchi1 .
have Pnorm i j : '[x_ i j] == 1 by rewrite cfnorm_dchi.
have Pvchar := dcTIirr_vchar.
have PC i j i' j' : '[x_ i j, x_ i' j'] = '[x_ i' j', x_ i j].
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
have P1 i j : '[1, x_ i j] == ((i == 0) && (j == 0))%:R.
  rewrite -dchi1 cfdot_dchi.
  case: (boolP (i == 0))=> [/eqP-> | NZi];
       case: (boolP (j == 0))=> [/eqP-> | NZj].
  - by rewrite /dcTIirr !eqxx [dirr1 _ == _]eq_sym (negPf (ndirr_diff _)) subr0.
  - move: (bcTIirrM1 NZi1 NZj) (bcTIirr1 NZi1 NZj). 
    rewrite (dcTIrrDE NZi1 NZj) !{1}inE !negb_or !ndirrEK -!andbA. 
    by case/and3P => _ /negPf-> _ /and3P [_ /negPf-> _]; rewrite subrr.
  - move: (bcTIirrM1 NZi NZj1) (bcTIirr1 NZi NZj1). 
    rewrite (dcTIrrDE NZi NZj1) !{1}inE !negb_or !ndirrEK -!andbA. 
    case/and3P => /negPf HH1 _ _ /and3P [/negPf HH2 _ _].
    by rewrite HH1 HH2 subrr.
  move: (bcTIirrM1 NZi NZj) (bcTIirr1 NZi NZj). 
  rewrite (dcTIrrDE NZi NZj) !{1}inE !negb_or !ndirrEK -!andbA. 
  case/and3P => _ _ /negPf HH1 /and3P [_ _ /negPf HH2].
  by rewrite -{2}[dirr1 G]ndirrK ndirrEK HH1 HH2 subrr.
have TT i2 j2 (NZi2 : i2 != 0) (NZj2 : j2 != 0) :
   [&& i2 != 0 , j2 != 0 &  
       dirr_constt (beta_ i2 j2) ==
       [set ndirr (dcTIirr i2 0); ndirr (dcTIirr 0 j2); dcTIirr i2 j2]].
  by rewrite NZi2 NZj2 /=; apply/eqP; apply: dcTIrrDE.
have Pjj' j j' : '[x_ 0 j, x_ 0 j'] == (j == j')%:R.
  case: (boolP (j == j')) => [/eqP->|]; first by rewrite Pnorm.
  case: (boolP (j == 0)) => [/eqP->| NZj] JdJ'.
    by rewrite P0 (eqP (P1 _ _)) [j' == _]eq_sym (negPf JdJ') eqxx.
  case: (boolP (j' == 0)) => [/eqP->| NZj'].
    by rewrite PC P0 (eqP (P1 _ _)) (negPf NZj) eqxx.
  move: (dA2r_diff h_beta_hyp JdJ' (TT _ _ NZi1 NZj) (TT _ _ NZi1 NZj')).
  by rewrite cfdot_dchi !ndirrEK => /andP [/negPf-> /negPf->]; rewrite subrr.
have Pii' i i' : '[x_ i 0, x_ i' 0] == (i == i')%:R.
  case: (boolP (i == i')) => [/eqP->|]; first by rewrite Pnorm.
  case: (boolP (i == 0)) => [/eqP->| NZi] IdI'.
    by rewrite P0 (eqP (P1 _ _)) [i' == _]eq_sym (negPf IdI') eqxx.
  case: (boolP (i' == 0)) => [/eqP->| NZi'].
    by rewrite PC P0 (eqP (P1 _ _)) (negPf NZi) eqxx.
  move: (dA2l_diff h_beta_hyp IdI' (dAsl (TT _ _ NZi NZj1))
             (dAsl (TT _ _ NZi' NZj1))).
  by rewrite cfdot_dchi !ndirrEK => /andP [/negPf-> /negPf->]; rewrite subrr.
have Pij i j : '[x_ i 0, x_ 0 j] == ((i == 0) && (j == 0))%:R.
  case: (boolP (i == 0))=> [/eqP-> | NZi]; first by rewrite P0 (eqP (P1 _ _)).
  case: (boolP (j == 0))=> [/eqP-> | NZj].
    by rewrite PC P0 (eqP (P1 _ _)) (negPf NZi) eqxx.
  case/andP: (dA_diff h_beta_hyp (TT _ _ NZi NZj)).
  by rewrite cfdot_dchi !ndirrEK => /negPf-> /negPf->; rewrite subrr.
have Pii'j i i' j : '[x_ i 0, x_ i' j] == ((i == i') && (j == 0))%:R.
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
have Pijj' i j j' : '[x_ 0 j, x_ i j'] == ((i == 0) && (j == j'))%:R.
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
by rewrite  subr0 eqr_nat.
Qed.

(* This is second_part of PeterFalvi (3.5). *)
Lemma dcTIirrE i j : i != 0 -> j != 0 ->
  'Ind[G, W] (alpha_ i j) = 1 - x_ i 0 - x_ 0 j + x_ i j.
Proof.
move=> NZi NZj.
rewrite -[X in X = _](subrK 1) -[_ - 1]/(beta_ i j).
by rewrite (dcTIrrE NZi NZj) addrC !addrA.
Qed.

End S3_5.

Local Notation x_ i j := (dchi (dcTIirr i j)).

Lemma card_cyclicTIset_pos : (0 < #|V|)%N.
Proof.
have F : (0 < #|W| - (w1 + w2))%N.
  rewrite subnDA -(dprod_card W1xW2) -/w2 -(subnKC tLW2) addSn subnS.
  by rewrite mulnSr addnK -/w1 -(subnKC tLW1) mulSnr addnK. 
apply: (leq_trans F).
rewrite cardsD leq_sub2l //.
apply: (leq_trans (subset_leq_card (subsetIr _ _))).
by rewrite cardsU leq_subr.
Qed.

Lemma norm_cyclicTIset : V <| W.
Proof.
case: tiW=> [_ _].
have DV : V != set0.
  by rewrite -card_gt0 card_cyclicTIset_pos.
case/(normedTI_P DV)=> _.
rewrite /normal subsetDl=> HH.
apply: subset_trans HH _.
by apply: subsetIr.
Qed.

Definition extIrrf (f : Iirr W -> 'CF(G)) (x : 'CF(W)) : 'CF(G) :=
  \sum_(i : Iirr W)  '[x, 'chi_i] *: (f i).

Lemma extIrrf_irr f i : extIrrf f 'chi_i = f i.
Proof.
rewrite /extIrrf (bigD1 i) /= ?(cfdot_irr,eqxx,scale1r) //.
by rewrite big1 ?addr0 //= => j Hij; 
   rewrite cfdot_irr eq_sym (negPf Hij) scale0r.
Qed.

Theorem extIrrf_is_linear f : linear (extIrrf f).
Proof.
move=> k /= x y.
rewrite /extIrrf.
rewrite scaler_sumr -big_split; apply: eq_bigr=> /= i _.
by rewrite cfdotDl cfdotZl scalerDl -scalerA.
Qed.

Canonical extIrrf_linear f : {linear 'CF(W) -> 'CF(G)} :=  
  Linear (extIrrf_is_linear f).

Definition cyclicTIsigma := locked
   (extIrrf_linear
    (oapp (fun  (f : {ffun Iirr W -> dIirr G}) i => dchi (f i)) (fun x: Iirr W => 0)
     [pick f : {ffun Iirr W -> dIirr G} |
       let g i := dchi (f i) in
       [&& orthonormal [image g x | x <- Iirr W], (f 0 == dirr1 _)
        &  all (fun a => 
                 'Ind[G, W] a == \sum_(i : Iirr W)  ('[a, 'chi_i] *: g i))
           (cfun_base W (W :\: (W1 :|: W2)))]])).

Local Notation sigma := cyclicTIsigma.

(* Move to character *)
Lemma inv_dprod_Iirr0 : inv_dprod_Iirr W1xW2 0 = (0,0).
Proof.
apply:  (can_inj (dprod_IirrK W1xW2)).
rewrite inv_dprod_IirrK /dprod_Iirr /= /irr_Iirr; case: pickP=> //= x.
by rewrite /cfDprod !chi0_1 cfDprodl1 cfDprodr1 mul1r irr_eq1 => /eqP->.
Qed.

(* This is PeterFalvi (3.2). *)
Lemma cyclicTIsigma_spec :
        [/\ 
         {in 'Z[irr W], isometry sigma, to 'Z[irr G]},
         sigma 1 = 1 &
         {in 'CF(W, V), forall a, sigma a = 'Ind[G, W] a}].
Proof.
rewrite /sigma; unlock.
rewrite /extIrrf; case: pickP=> [/= f /and3P [Ho H1 /allP /= HI]|].
  split=> [|| a /coord_span ->].
  - split=> [i j Hi Hj /=|i Hi]; last first.
      rewrite /extIrrf; apply: sum_zchar=> j _.
      repeat apply: scale_zchar; last by apply: irr_vchar.
        by apply: cfdot_vchar_irr_Int.
      by apply: isIntC_sign.
    rewrite /extIrrf.
    rewrite {2}[i]cfun_sum_cfdot {2}[j]cfun_sum_cfdot.
    rewrite !cfdot_suml; apply: eq_bigr=> i1 _.
    rewrite !cfdot_sumr; apply: eq_bigr=> j1 _.
    rewrite cfdotZl [X in _ = X]cfdotZl; congr (_ * _).
    rewrite cfdotZr [X in _ = X]cfdotZr; congr (_ * _).
    case/orthonormalP: Ho=> Hu Hv; rewrite Hv; last 2 first.
      by apply/imageP; exists i1.
      by apply/imageP; exists j1.
    rewrite cfdot_irr.
    case: (boolP (_ == _)); case: (boolP (i1 == j1))=> //; last first.
      by move/eqP->; rewrite eqxx.
    move=> Eqi /eqP Eqch; case/eqP: Eqi.
    by move/injectiveP: Hu; apply.
  - rewrite /extIrrf (bigD1 (0 : Iirr W)) // (eqP H1) /= dchi1.
    rewrite -![1]chi0_1 cfdot_irr eqxx scale1r chi0_1 big1 ?addr0 // => i Hi.
    by rewrite cfdot_irr eq_sym (negPf Hi) scale0r.
  rewrite /extIrrf linear_sum /=.
  set l :=  [image _ | _ <- _]; set c := coord _; set n := #|_|.
  pose FF i := \sum_(j < n) '[ c j a *: l`_j, 'chi_i] *: dchi (f i).
  rewrite (eq_bigr FF)=> [| i _]; last first.
    by rewrite cfdot_suml scaler_suml; apply: eq_bigr=> j _.
  rewrite exchange_big /=; apply: eq_bigr=> i _.
  rewrite linearZ /= (eqP (HI _ _)) //.
    rewrite scaler_sumr; apply: eq_bigr=> j _.
    by rewrite cfdotZl !scalerA !mulrA.
  by apply: mem_nth; rewrite size_image.
pose p i := (inv_dprod_Iirr W1xW2 i).
pose tt : {ffun Iirr W -> dIirr G} :=
   [ffun k : Iirr W => dcTIirr (p k).1 (p k).2].
have d00 : dcTIirr 0 0 = dirr1 _ by rewrite /dcTIirr !eqxx.
move/(_ tt)=> /idP []; apply/and3P; split.
- apply/orthonormalP; split.
    apply/injectiveP=> /= u v /dchi_inj; rewrite !ffunE => HH.
    move: (cfdot_dcTIirr (p u).1 (p u).2 (p v).1 (p v).2).
    rewrite {1}HH; rewrite cfdot_dcTIirr !eqxx.
    move: (inv_dprod_IirrK W1xW2 u) (inv_dprod_IirrK W1xW2 v).
    rewrite /p; case: (inv_dprod_Iirr _ _)=> /= i1 j1 <-.
    case:  (inv_dprod_Iirr _ _)=> /= i2 j2 <-.
    case: (_ =P _)=> [->| _ /eqP]; last by rewrite oner_eq0.
    by case: (_ =P _)=> [-> //| _ /eqP]; rewrite andbF oner_eq0.
  move=> u v /imageP [i Hi ->] /imageP [j Hj ->].
  case: (_ =P _)=> [->|]; first by rewrite ffunE cfdot_dcTIirr !eqxx.
  rewrite !ffunE cfdot_dcTIirr => HH.
  case: (_ =P _)=> [/=|//] HHi; case: (_ =P _)=> [/= | //] HHj.
  by case: HH; rewrite HHi HHj.
- by rewrite ffunE /p inv_dprod_Iirr0 /= d00 //.
apply/allP=> /= u Hu.
have: u \in 'CF(W,V) by apply: memv_span.
move/(coord_basis acTIirr_base_basis)->; apply/eqP.
set t := image_tuple _ _; set c := coord t.
pose FF i :=  \sum_j (c j u *: (('[t`_j, 'chi_i] *: dchi (tt i)))).
rewrite (eq_bigr FF)=> [|i1 _]; last first.
  rewrite cfdot_suml scaler_suml; apply: eq_bigr=> i2 _.
  by rewrite cfdotZl !scalerA.
rewrite linear_sum exchange_big; apply: eq_bigr=> j _ /=.
rewrite linearZ -scaler_sumr /=; congr (_ *: _).
set l := image _ _.
have /imageP[[i1 j1]]: l`_j \in l by apply: mem_nth; rewrite size_image.
rewrite !inE /= => /andP [Hi1 Hj2]  ->.
rewrite dcTIirrE //.
set ss := \sum_(i < _) _. 
have->: ss = (extIrrf (fun i => dchi (tt i)) (alpha_ i1 j1)) by done.
rewrite acTIirrE !(linearD, linearB, linearN).
by rewrite -![1]chi0_1 !cTIirrE /= !extIrrf_irr !ffunE /p /= !dprod_IirrK 
           inv_dprod_Iirr0 /= chi0_1 d00 dchi1.
Qed.

Lemma cyclicTIisometry : {in 'Z[irr W], isometry sigma, to 'Z[irr G]}.
Proof. by case: cyclicTIsigma_spec. Qed.

Lemma cyclicTIsigma_ind : {in 'CF(W, V), forall a, sigma a = 'Ind[G, W] a}.
Proof. by case: cyclicTIsigma_spec. Qed.

Lemma cyclicTIsigma1 : sigma 1 = 1.
Proof. by case: cyclicTIsigma_spec. Qed.

Lemma cyclicTIsigma_restrict a : {in V, sigma a =1 a}.
Proof.
have F1 i j : '[sigma ('chi_i), sigma ('chi_j)] = (i == j)%:R.
  by case: cyclicTIisometry=> ->; rewrite ? irr_vchar // cfdot_irr.
case: (equiv_restrict_compl_ortho _ _ acTIirr_base_basis F1)
     => [||j|Er1 Er2 v Hv] //.
- by case: tiW=> [[]].
- by apply: norm_cyclicTIset.
- set l := image_tuple _ _.
  have Hj: l`_j \in 'CF(W,V).
    apply: (basis_mem acTIirr_base_basis).
    by apply: mem_nth; rewrite size_image.
  rewrite -cyclicTIsigma_ind // [l`_j]cfun_sum_cfdot linear_sum.
  by apply: eq_bigr=> i _ //; rewrite -cfun_sum_cfdot linearZ.
rewrite [a]cfun_sum_cfdot linear_sum !sum_cfunE; apply: eq_bigr=> i _.
by rewrite linearZ !cfunE Er1.
Qed.

Lemma cyclicTIsigma_orthogonal z : 
  (forall i, '[z, sigma 'chi[W]_i] = 0) -> {in V, forall x, z x = 0}.
Proof.
have F1 i j : '[sigma ('chi_i), sigma ('chi_j)] = (i == j)%:R.
  by case: cyclicTIisometry=> ->; rewrite ? irr_vchar // cfdot_irr.
case: (equiv_restrict_compl_ortho _ _ acTIirr_base_basis F1)
     => [||j|Er1 Er2 Ho] //.
- by case: tiW=> [[]].
- by apply: norm_cyclicTIset.
- set l := image_tuple _ _.
  have Hj: l`_j \in 'CF(W,V).
    apply: (basis_mem acTIirr_base_basis).
    by apply: mem_nth; rewrite size_image.
  rewrite -cyclicTIsigma_ind // [l`_j]cfun_sum_cfdot linear_sum.
  by apply: eq_bigr=> i _ //; rewrite -cfun_sum_cfdot linearZ.
by apply: Er2=> i; exact: Ho.
Qed.

(* This is PeterFalvi (3.7). *)
Lemma cyclicTI_dot_sum (phi : 'CF(G)) i1 i2 j1 j2 :
  {in V, forall x, phi x = 0} -> 
   '[phi, sigma (w_ i1 j1)] + '[phi, sigma (w_ i2 j2)] =
   '[phi, sigma (w_ i1 j2)] + '[phi, sigma (w_ i2 j1)].
Proof.
move=> ZphiV.
pose a : 'CF(W) := w_ i1 j1 + w_ i2 j2 - w_ i1 j2 - w_ i2 j1.
have LW1 := cTIirr_linearW1; have LW2 := cTIirr_linearW2.
have Cfa : a \in 'CF(W, V).
  apply/cfun_onP=> g.
  rewrite inE negb_and negbK !inE -orbA 
          => /or3P [GiW1|GiW2|GniW]; last by rewrite cfun0.
    rewrite -[g]mulg1  /a !cTIirrE !dprod_IirrE !cfunE.
    rewrite !cfDprodEl // !cfDprodEr // !lin_char1 // !mulr1.
    by rewrite addrAC addrK subrr.
  rewrite -[g]mul1g  /a !cTIirrE !dprod_IirrE !cfunE.
  rewrite !cfDprodEl // !cfDprodEr // !lin_char1 // !mul1r.
  by rewrite addrK subrr.
suff: '[phi, 'Ind[G] a] == 0.
  rewrite -!cyclicTIsigma_ind // !linearB !linearD !cfdot_subr !cfdotDr.
  by rewrite -addrA -opprD subr_eq0=> /eqP.
rewrite cfdotE big1 ?mulr0 // => g GiG.
case: (boolP (g \in class_support V G))=> [/imset2P [v h ViV HiG ->]|GniC].
  by rewrite cfunJ // ZphiV // mul0r.
have /cfun_onP-> //: 'Ind[G] a \in 'CF(G, class_support V G).
  by apply: cfInd_on=> //; case: tiW=> [[]].
by rewrite conjC0 mulr0.
Qed.

Lemma cfdot_sigma i1 i2 j1 j2 : 
  '[sigma(w_ i1 j1), sigma(w_ i2 j2)] = ((i1 == i2) && (j1 == j2))%:R.
Proof.
case: cyclicTIisometry=> ->; rewrite ?irr_vchar // => _.
rewrite !cTIirrE cfdot_irr.
case: (boolP (i1 == _))=> [/eqP->|I1dI2]; last first.
  case: (boolP (_ == _))=> // /eqP /dprod_Iirr_inj.
  by case=> HH; case/eqP: I1dI2.
case: (boolP (j1 == _))=> [/eqP->|Dj1j2]; first by rewrite eqxx.
case: (boolP (_ == _))=> // /eqP /dprod_Iirr_inj.
by case=> HH; case/eqP: Dj1j2.
Qed.

Lemma cfdot_sigma_eq i1 i2 j1 j2 :
   '[sigma (w_ i1 j1), sigma (w_ i2 j2)] = 
           (sigma (w_ i1 j1) == sigma (w_ i2 j2))%:R.
Proof.
case: (boolP (_ == _))=> [/eqP <-|]; rewrite cfdot_sigma ?eqxx //.
case: (boolP (i1 == _))=>[/eqP <- |//].
by case: (boolP (j1 == _))=>[/eqP <- /negP []|].
Qed.

Lemma sigma_eqE i1 i2 j1 j2 : 
  (sigma (w_ i1 j1) == sigma (w_ i2 j2)) = ((i1 == i2) && (j1 == j2)).
Proof.
apply/eqP/idP=> [Hs|].
  have: '[sigma (w_ i1 j1)] == 1 by rewrite cfdot_sigma ?eqxx.
  rewrite  {2}Hs cfdot_sigma pnatr_eq1.
  by case: (i1 == _)=> //; case: (j1 == _).
by case/andP=> /eqP-> /eqP->.
Qed.

Lemma sigma_opp_neq i1 i2 j1 j2 : 
  (sigma (w_ i1 j1) == -sigma (w_ i2 j2)) = false.
Proof.
apply/negP=> HH.
have: '[sigma (w_ i1 j1)] = 1 by rewrite cfdot_sigma ?eqxx.
rewrite  {1}(eqP HH) cfdotNl cfdot_sigma.
case: (_ == _)=> /eqP; last by rewrite oppr0 eq_sym oner_eq0.
case: (j2 == _); last by rewrite oppr0 eq_sym oner_eq0.
by rewrite eq_sym -subr_eq0 opprK -(natrD _ 1) pnatr_eq0.
Qed.

Lemma dirr_sigma i j : sigma(w_ i j) \in dirr G.
Proof.
apply: dirr_norm1; last by rewrite cfdot_sigma !eqxx.
case:  cyclicTIisometry=> _; apply.
by apply: irr_vchar.
Qed.
 
(* NC as defined in PeterFalvi (3.6). *)
Definition cyclicTI_NC phi := #|[set ij | '[phi, sigma (w_ ij.1 ij.2)] != 0]|.
Local Notation NC := cyclicTI_NC.

Lemma cyclicTI_NC_opp (phi : 'CF(G)) : (NC (-phi)%R = NC phi)%N.
Proof. by apply: eq_card=> [[i j]]; rewrite !inE cfdotNl oppr_eq0. Qed.

Lemma cyclicTI_NC_sign (phi : 'CF(G)) n : (NC ((-1) ^+ n *: phi)%R = NC phi)%N.
Proof. 
elim: n=> [|n IH]; rewrite ?(expr0,scale1r) //.
by rewrite exprS -scalerA scaleN1r cyclicTI_NC_opp.
Qed.

Lemma cyclicTI_NC_sigma i j : NC (sigma (w_ i j)) = 1%N.
Proof.
rewrite -(cards1 (i,j)); apply: eq_card=> [[i1 j1]]; rewrite !inE.
rewrite cfdot_sigma //= pnatr_eq0.
case: (i =P _)=> [->|IdI1 /=].
  case: (j =P _)=> [-> |Djj1 /=]; first by rewrite eqxx.
  by case: (_ =P _)=> // [[]] HH; case: Djj1.
by case: (_ =P _)=> // [[]] HH; case: IdI1.
Qed.

Lemma cyclicTI_NC_irr i : (NC 'chi_i <= 1)%N.
Proof.
case:  cyclicTIisometry=> Isig Zsig.
have: (0 <= NC 'chi_i)%N by done.
rewrite leq_eqVlt; case/orP=> [/eqP-> //|/card_gt0P [[i1 j1]]].
rewrite inE cfdot_dirr ?(dirr_chi, dirr_sigma) //=.
case: ('chi_i =P _)=> [->|_].
  by rewrite cyclicTI_NC_opp cyclicTI_NC_sigma.
by case: ('chi_i =P _)=> [->|_]; rewrite ?(cyclicTI_NC_sigma, eqxx).
Qed.

Lemma cyclicTI_NC_dirr f : f \in dirr G -> (NC f <= 1)%N.
Proof.
by case/orP; last rewrite -cyclicTI_NC_opp; case/irrP=> i ->;
   exact: cyclicTI_NC_irr.
Qed.

Lemma cyclicTI_NC_add (phi psi : 'CF(G)) : 
  (NC (phi + psi)%R <= NC phi + NC psi)%N.
Proof.
rewrite -cardsUI; apply: leq_trans (leq_addr _ _).
rewrite subset_leqif_card //; apply/subsetP=> [[i j]]; rewrite !inE /= => HH.
(do 2 (case: (_ =P _)=> //))=> HH1 HH2; case/negP: HH.
by rewrite cfdotDl HH1 HH2 add0r.
Qed.

Lemma cyclicTI_NC_sub (phi psi : 'CF(G)) : 
  (NC (phi - psi)%R <= NC phi + NC psi)%N.
Proof. by move: (cyclicTI_NC_add phi (-psi)); rewrite cyclicTI_NC_opp. Qed.

(* This is PeterFalvi (3.8). *)
Lemma cyclicTI_NC_split (phi : 'CF(G)) i j : 
  {in V, forall x, phi x = 0} -> (NC phi < 2 * minn w1 w2)%N ->
  '[phi, sigma (w_ i j)] != 0 ->    
   {(forall i1 j1,
       '[phi, sigma (w_ i1 j1)] = (j == j1)%:R * '[phi, sigma (w_ i j)])}
   +
   {(forall i1 j1 ,
      '[phi, sigma (w_ i1 j1)] = (i == i1)%:R * '[phi, sigma (w_ i j)])}.
Proof.
move=> ZphiV NC_M NZaij.
pose a i j := '[phi, sigma (w_ i j)].
have CDS i1 i2 j1 j2 : a i1 j1 + a i2 j2 = a i1 j2 + a i2 j1.
  by apply: cyclicTI_dot_sum.
pose S := [set ij | a ij.1 ij.2 != 0].
pose L j :=  [set ij | ij.2 == j] :&: S.
pose C i :=  [set ij | ij.1 == i] :&: S.
have LsS j1 : C j1 \subset S by apply: subsetIr.
have CsS i1 : L i1 \subset S by apply: subsetIr.
have LI i1 i2 : L i1 :&: L i2 = if i1 == i2 then L i1 else set0.
  apply/setP=> [[i3 j3]]; case: (boolP (i1 == i2)) => [/eqP->|];
           rewrite !inE ?andbb //= => HH.
  by apply/idP=> /andP [] /andP [/eqP -> _]; rewrite (negPf HH).
have CI i1 i2 : C i1 :&: C i2 = if i1 == i2 then C i1 else set0.
  apply/setP=> [[i3 j3]]; case: (boolP (i1 == i2)) => [/eqP->|];
           rewrite !inE ?andbb //= => HH.
  by apply/idP=> /andP [] /andP [/eqP -> _]; rewrite (negPf HH).
have LCI i1 j1 : (L j1 :&: C i1) \subset [set (i1,j1)].
  apply/subsetP=> [[i2 j2]]; rewrite !inE /=.
  by case/andP=> /andP [/eqP-> _] /andP [/eqP-> _].
have FC i1: (forall j, a i1 j != 0) -> #|C i1| = w2.
   move=> FF.
  have<-: #|[image (i1,j) | j <- Iirr W2]| = w2.
    rewrite card_in_image=> [|i3 i4 i3Irr i4Irr /= [] //].
    by rewrite card_ord NirrE classesW2.
  apply: eq_card=> [[i3 j3]]; rewrite !inE /=; apply/andP/imageP.
    by case=> /eqP-> _; exists j3.
  by case=> j4 j4Irr [] -> ->.
  (* This is 3.8.1 *)
have EqI i1 i2 j1 j2 : a i1 j2 == 0 -> a i2 j1 == 0 -> a i1 j1 == 0.
  case: (boolP (i1 == i2))=> [/eqP-> // | I1dI2].
  case: (boolP (j1 == j2))=> [/eqP-> // | Dj1j2].
  move=> Zai1j2 Zai2j1; case: (boolP (_ == _)) => // NZa1j1.
  move: NC_M; rewrite ltnNge; case/negP.
  pose LS := 
    [set x \in [image (if a k j1 == 0 then 
                          (k, j2) else (k, j1)) | k <- Iirr W1]].
  have LSsS : LS \subset S.
    apply/subsetP=> p; rewrite inE => /imageP [k KiIw1->].
    rewrite inE; case: (boolP (a k j1 == 0))=> //= Zakj1.
    apply: contra NZa1j1 => Zakj2.
    move: (CDS i1 k j1 j2).
    by rewrite (eqP Zakj2) (eqP Zai1j2) (eqP Zakj1) !addr0=> /eqP.
  have cardLS: #|LS| = w1.
    by rewrite cardsE card_in_image=> [|j3 j4 j3Irr j4Irr /=]; 
        [rewrite card_ord NirrE | do 2 case: (_ == _); case].
  pose CS := 
     [set x \in [image (if a i1 k == 0 then 
                          (i2, k) else (i1, k)) | k <- Iirr W2]].
  have CSsS : CS \subset S.
    apply/subsetP=> p; rewrite inE => /imageP [k KiIw2->].
    rewrite inE; case: (boolP (a i1 k == 0))=> //= Zai1k.
    apply: contra NZa1j1 => Zai2k.
    move: (CDS i1 i2 k j1).
    by rewrite (eqP Zai1k) (eqP Zai2j1) (eqP Zai2k) !addr0 => <-.
  have cardCS: #|CS| = w2.
    by rewrite cardsE card_in_image=> [|i3 i4 i3Irr i4Irr /=]; 
        [rewrite card_ord NirrE | do 2 case: (_ == _); case].
  have /subset_leqif_card[HH _]: LS :|: CS \subset S.
    by apply/subUsetP; split.
  apply: leq_trans HH; rewrite cardsU cardLS cardCS.
  rewrite -[X in (X <= _)%N](addnK #|LS :&: CS|) leq_sub2r //.
  have: (#|LS :&: CS| <= 2)%N.
    suff: LS :&: CS \subset [set (i1,j1); (i2,j2)].
      case/subset_leqif_card; rewrite cards2; case: ((_,_) =P _)=> // [[UU ]].
      by case/eqP: I1dI2.
    apply/subsetP=> u.
    rewrite !inE => /andP [] /imageP [i3 i3Irr ->] /imageP [i4 i4Irr].
    by (do 2 case: (a _ _ =P _))=> Eq1 Eq2 [] Eq3 Eq4;
       move: Eq1 Eq2; rewrite Eq3 -Eq4 ?(eqxx, orbT) // => *; case/eqP: NZa1j1.
  rewrite -(leq_add2l (2 * minn w1 w2)); move/leq_trans; apply.
  move: oddW1 oddW2 cyclicTI_coprime tLW1 tLW2; rewrite -/w1 -/w2.
  move: w1 w2=> u1 v1; wlog: u1 v1 / (u1 < v1)%N 
        => [WW O1 O2 CP tLU1 tLV1|WW O1 O2 CP tLU1 tLV1].
    case: (ltngtP u1 v1)=> Hl; first by apply: WW.
      by rewrite minnC [(u1 + _)%N]addnC WW // coprime_sym.
    by move: CP tLV1; rewrite Hl /coprime gcdnn => /eqP->.
  rewrite /minn WW mulSn mul1n -addnA leq_add2l addnC.
  move: WW O2; rewrite leq_eqVlt => /orP [/eqP<-|] //.
  by rewrite /odd /=; case/negP.
have cardLE i1 j1 j2 : a i1 j1 != 0 -> a i1 j2 == 0 -> #|L j1| = w1.
  move=> NZai1j1 Zai1j2.
  have <-: #|[image (i,j1) | i <- Iirr W1]| = w1.
    by rewrite card_in_image=> [| i2 i3 _ _ [] //]; rewrite card_ord NirrE.
  apply: eq_card=> [[i3 j3]]; rewrite !inE; apply/andP/imageP=> /=.
    by case=> /eqP-> _; exists i3.
  case=> i2 i2Irr [] -> ->; split=> //.
  by apply: contra NZai1j1; apply: EqI Zai1j2.
have cardCE i1 i2 j1 : a i1 j1 != 0 -> a i2 j1 == 0 -> #|C i1| = w2.
  move=> NZai1j1 Zai2j1.
  have <-: #|[image (i1,j) | j <- Iirr W2]| = w2.
    by rewrite card_in_image=> [| j2 j3 _ _ [] //]; rewrite card_ord NirrE.
  apply: eq_card=> [[i3 j3]]; rewrite !inE; apply/andP/imageP=> /=.
    by case=> /eqP-> _; exists j3.
  case=> j2 j2Irr [] -> ->; split=> //.
  by apply: contra NZai1j1 => /EqI /(_ Zai2j1).
have BLe i1 j1: (2 * minn w1 w2 <= w1 + w2 - #|L j1 :&: C i1|)%N.
  rewrite -[X in (X <= _)%N](addnK #|L j1 :&: C i1|) leq_sub2r //.
  have: (#|L j1 :&: C i1| <= 1)%N.
    by have:= LCI i1 j1; case/subset_leqif_card; rewrite cards1.
  rewrite -(leq_add2l (2 * minn w1 w2)); move/leq_trans; apply.
  rewrite addnC mulSn mul1n !addnA /minn; case: ltngtP=> HL.
  - by rewrite leq_add2r //.
  - by rewrite addnC leq_add2l //.
  move: cyclicTI_coprime tLW1.
  by rewrite -/w1 -/w2 HL /coprime gcdnn => /eqP->.
case: (boolP (forallb j1 : Iirr W2, (a i j1 != 0)))=> HH; last first.
  (* This is 3.8.2 *)
  left; move: HH; rewrite negb_forall => /existsP [j1].
  rewrite negbK => Zaij1.
  have Dj1j : j1 != j by apply: contra NZaij => /eqP<-.
  have EC: C i = [set (i, j)].
    apply/setP=> [[i2 j2]]; rewrite !inE /=.
    apply/andP/eqP=> [[/eqP-> NZaij2] |[-> ->]] //.
    case: (boolP (j2 == j))=> [/eqP-> //| J2dJ].
    move: NC_M; rewrite ltnNge; case/negP.
    have /subset_leqif_card[HH _]: L j :|: L j2 \subset S.
      by apply/subUsetP.
    apply: leq_trans HH; rewrite cardsU !(cardLE _ _ _ _ Zaij1) //.
    rewrite LI eq_sym (negPf J2dJ) cards0 subn0.
    by rewrite mulSn mul1n leq_add ?geq_minl ?geq_minr.
  suff HL i2 j2 : j != j2 -> a i2 j2 = 0.
     move=> i2 j2; case: (boolP (_ == _))=> [/eqP <-| Djj2]; last first.
       by move: (HL i2 _ Djj2); rewrite mul0r.
     rewrite mul1r; case: (boolP (i2 == i))=> [/eqP-> //| Di2i].
    move: (CDS i i2 j j1).
    by rewrite !(HL _ j1) 1?eq_sym // addr0 add0r.
  move=> Djj2; case: (boolP (a i2 j2 == 0))=> [/eqP-> // | NZai2j2].
  have cardC : #|C i2| = w2.
    apply: (cardCE _ i _ NZai2j2).
    have: (i,j2) \notin C i.
      by rewrite EC !inE; apply: contra Djj2=> /eqP [] ->.
    by rewrite !inE eqxx /= negbK.
  have cardL : #|L j| = w1  by apply: (cardLE _ _ j1 NZaij)=> //.
  move: NC_M; rewrite ltnNge; case/negP.
  have /subset_leqif_card[HH _]: L j :|: C i2 \subset S.
    by apply/subUsetP; split.
  by apply: leq_trans HH; rewrite cardsU cardC cardL.
 (* This is 3.8.3 *)
right; move/forallP: HH => HH.
suff HL i1 j1 : i != i1 -> a i1 j1 = 0.
  move=> i1 j1; case: (boolP (_ == _))=> [/eqP <-| IdI1]; last first.
    by move: (HL _ j1 IdI1); rewrite mul0r.
  rewrite mul1r; case: (boolP (j1 == j))=> [/eqP-> //| J2dJ].
  have: (2 < #|Iirr W1|)%N by rewrite card_ord //  NirrE classesW1.
  rewrite (cardD1 i) !inE !ltnS=> Hv.
  case/card_gt0P: (ltn_trans (is_true_true : 0 < 1)%N Hv)=> i2.
  rewrite !inE andbT=> Di2i.
  move: (CDS i i2 j j1).
  by rewrite !(HL i2) 1?eq_sym // !addr0.
move=> IdI1; case: (boolP (a i1 j1 == 0))=> [/eqP //| NZai1j1].
case: (boolP (forallb j2 : Iirr W2, (a i1 j2 != 0))); last first.
  rewrite negb_forall => /existsP [] j2; rewrite negbK => Zai1j2.
  move: NC_M; rewrite ltnNge; case/negP.
  have /subset_leqif_card[HH1 _]: L j1 :|: C i \subset S.
    by apply/subUsetP.
  by apply: leq_trans HH1; rewrite cardsU FC // !(cardLE _ _ _ _ Zai1j2).
move/forallP=> HH1.
move: NC_M; rewrite ltnNge; case/negP.
have /subset_leqif_card[HH2 _]: C i :|: C i1 \subset S.
  by apply/subUsetP.
apply: leq_trans HH2; rewrite cardsU !FC // CI (negPf IdI1) cards0 subn0.
by rewrite mulSn mul1n leq_add ?geq_minl ?geq_minr.
Qed.

(* a weaker version of PeterFalvi (3.8). *)
Lemma cyclicTI_NC_minn (phi : 'CF(G)) : 
  {in V, forall x, phi x = 0} -> (0 < NC phi < 2 * minn w1 w2)%N ->
   (minn w1 w2 <= NC phi)%N.
Proof.
move=> ZphiV /andP []; rewrite card_gt0 => /set0Pn [[i1 j1]].
rewrite inE /= => NZs NN.
pose a i j := '[phi, sigma (w_ i j)].
pose S := [set ij | a ij.1 ij.2 != 0].
pose L :=  [set (i1, j) | j <- Iirr W2].
have cL : #|L| = w2.
  by rewrite card_imset ?(card_ord, NirrE) // => i j [].
pose C :=  [set (i, j1) | i <- Iirr W1].
have cC : #|C| = w1.
  by rewrite card_imset ?(card_ord, NirrE) // => i j [].
case/(cyclicTI_NC_split ZphiV NN): (NZs) => HH.
- suff: C \subset S.
    case/subset_leqif_cards; rewrite cC => LC _.
    by apply: leq_trans LC; rewrite geq_minl.
  apply/subsetP=> [[i2 j2]]; rewrite !inE /a.
  case/imsetP=> j3 J3Irr [] -> -> /=.
  by rewrite HH eqxx mul1r NZs.
suff: L \subset S.
  case/subset_leqif_cards; rewrite cL => LL _.
  by apply: leq_trans LL; rewrite geq_minr.
apply/subsetP=> [[i2 j2]]; rewrite !inE /a.
case/imsetP=> j3 J3Irr [] -> -> /=.
by rewrite HH eqxx mul1r NZs.
Qed.

(* This is PeterFalvi (3.9a). *)
Lemma cyclicTI_dirr (i : Iirr W) (phi : 'CF(G)) :
  phi \in dirr G -> {in V, phi =1 'chi_i} -> phi = sigma 'chi_i.
Proof.
move=> Dphi; rewrite -(inv_dprod_IirrK W1xW2 i).
case: (inv_dprod_Iirr _)=> /= i1 j1; rewrite -cTIirrE => EphiC.
pose psi : 'CF(G) := sigma (w_ i1 j1) - phi.
have ZpsiV: {in V, forall g, psi g = 0}=> [g GiV|].
  by rewrite /psi !cfunE cyclicTIsigma_restrict // -(EphiC _ GiV) subrr.
pose a i j := '[psi, sigma (w_ i j)].
pose S := [set ij | a ij.1 ij.2 != 0].
case: (boolP ((i1, j1) \in S))=> [I1J1iS|]; last first.
  rewrite inE negbK /a  cfdot_subl cfdot_sigma !eqxx /=.
  rewrite cfdot_dirr ?(dirr_chi, dirr_sigma) //.
  case: (boolP (phi == _))=> [|_].
    by rewrite opprK -(natrD _ 1 1) pnatr_eq0.
  case: (boolP (phi == _))=> [/eqP //|].
  by rewrite subr0 oner_eq0.
have SPos : (0 < #|S|)%N by rewrite (cardD1 (i1,j1)) I1J1iS.
have SLt: (#|S| <= 2)%N.
  rewrite -[2%N]add1n; apply: leq_trans (cyclicTI_NC_sub _ _) _.
  by rewrite leq_add // !cyclicTI_NC_dirr // dirr_sigma.
have: (0 < #|S| < 2 * minn w1 w2)%N.
  rewrite SPos; apply: leq_ltn_trans SLt _.
  by rewrite -{1}[2%N]muln1 ltn_mul2l /= leq_min ![(1 < _)%N]ltnW.
move/(cyclicTI_NC_minn ZpsiV); rewrite leqNgt; case/negP.
by apply: leq_ltn_trans SLt _; rewrite leq_min tLW1.
Qed.

Lemma cyclicTIirrP chi : chi \in irr W -> {i : Iirr W1 & {j | chi = w_ i j}}.
Proof.
case/irrP/sig_eqW=> ij ->{chi}; rewrite -[ij](inv_dprod_IirrK W1xW2).
by case: {ij}(inv_dprod_Iirr _ _) => i j; exists i, j; rewrite cTIirrE.
Qed.

Lemma cycTIirr_aut u i j : w_ (aut_Iirr u i) (aut_Iirr u j) = cfAut u (w_ i j).
Proof.
apply/esym/cfun_inP=> x; have /dprodP[_ {1}<- _ _] := W1xW2.
case/mulsgP=> x1 x2 Wx1 Wx2 ->; rewrite !cTIirrE 2!dprod_IirrE.
by rewrite cfunE 2?cfDprodE // rmorphM !aut_IirrE !cfunE.
Qed.

(* This is the second part of Peterfalvi (3.9a). *)
Lemma cfAut_cycTIiso u phi : cfAut u (sigma phi) = sigma (cfAut u phi).
Proof.
rewrite [phi]cfun_sum_cfdot !raddf_sum; apply: eq_bigr => ij _.
rewrite /= !(linearZ, cfAutZ) /= -aut_IirrE; congr (_ *: _) => {phi}.
apply: cyclicTI_dirr => [|x Vx /=].
  by have /cyclicTIirrP[i [j ->]] := irr_chi ij; rewrite dirr_cfAut dirr_sigma.
by rewrite cfunE cyclicTIsigma_restrict // aut_IirrE cfunE.
Qed.

End Proofs.

Lemma cyclicTIsigma_sym (gT : finGroupType) (G W W1 W2 : {group gT}) : 
   cyclicTIsigma G W W1 W2  = cyclicTIsigma G W W2 W1.
Proof. by rewrite /cyclicTIsigma setUC. Qed.
