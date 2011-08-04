(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter frobenius PFsection1 PFsection2.

(******************************************************************************)
(* This file covers Peterfalvi, Section 3: TI-Subsets with Cyclic Normalizers *)
(* Defined here:                                                              *)
(*   cylicTIhypothesis G W W1 W2 == W1 \x W2 = W is a cyclic subgroup of G,   *)
(*                           W1 and W2 are nontrivial of coprime order, and   *)
(*                           W :\: (W1 :|: W2) is a non-empty TI subset of G. *)
(*                           This is Peterfalvi (3.1).                        *)
(* For ccW : cylicTIhypothesis G W W1 W2 we set                               *)
(*        cyclicTIset ccW == W :\: (W1 :|: W2)                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Definitions.

Variables (gT : finGroupType) (G W W1 W2 Wi : {set gT}).

Definition cyclicTIhypothesis :=
  [/\ [/\ W1 \x W2 = W, cyclic W, odd #|W| & W \subset G],
      [/\ W1 != 1, W2 != 1 & coprime #|W1| #|W2| ]
    & normedTI (W :\: (W1 :|: W2)) G W]%g.

Definition cyclicTIset of cyclicTIhypothesis := W :\: (W1 :|: W2).

End Definitions.

Section Proofs.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).

Hypothesis tiW : cyclicTIhypothesis G W W1 W2.

Lemma cyclicTIhyp_sym : cyclicTIhypothesis G W W2 W1.
Proof. by case: tiW; rewrite dprodC coprime_sym setUC => ? []. Qed.

Let w1 := #|W1|.
Let w2 := #|W2|.
Let V := cyclicTIset tiW.

Let W1xW2 :  W1 \x W2 = W.
Proof. by case: tiW; case. Qed.

Let cyclicW : cyclic W.
Proof. by case: tiW; case. Qed.

Let cyclicW1 : cyclic W1.
Proof.
apply: cyclicS cyclicW.
by case/dprodP: W1xW2=> _ <- _ _; apply: mulg_subl (group1 _).
Qed.

Let cyclicW2 : cyclic W2.
Proof.
apply: cyclicS cyclicW.
by case/dprodP: W1xW2=> _ <- _ _; apply: mulg_subr (group1 _).
Qed.

Let oddW1 : odd #|W1|.
Proof. by case: tiW=> [[]] /dprod_card <- _; rewrite odd_mul; case/andP. Qed.

Let oddW2 : odd #|W2|.
Proof. by case: tiW=> [[]] /dprod_card <- _; rewrite odd_mul; case/andP. Qed.

Let tLW1 : (2 < #|W1|)%N.
Proof.
by case: tiW=> _ []; rewrite -!cardG_gt1; case: #|_| oddW1=> [|[|[]]]. 
Qed.

Let tLW2 : (2 < #|W2|)%N.
Proof.
by case: tiW=> _ []; rewrite -!cardG_gt1; case: #|_| oddW2=> [|[|[]]]. 
Qed.

(* GG : You cannot use w_ as a GLOBAL IDENTIFIER !!! *)
(* This should also apply to the name of global lemmas below and to the      *)
(* definition of alpha_ and beta.                                            *)
Definition cyclicTIirr i j := 'chi_(dprod_Iirr W1xW2 (i, j)).
Local Notation w_ := cyclicTIirr.

Lemma w00 : w_ 0 0 = 1.
Proof.
rewrite /w_ dprod_IirrE !chi0_1.
apply/cfun_inP=> x Wx; rewrite cfun1E Wx.
case/(mem_dprod W1xW2): Wx => y [z [W1y W2z -> _]].
by rewrite cfDprodE // !cfun1E W1y W2z mulr1.
Qed.

Lemma w_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof. by rewrite /w_ !dprod_IirrE !chi0_1 cfDprod1r cfDprod1l. Qed.

Let linearX (i : Iirr W) : lin_char ('chi_i).
Proof.
apply/char_abelianP.
by apply: cyclic_abelian; case: tiW; case.
Qed.

Definition alpha_ i j : 'CF(W) := (1 - w_ i 0) * (1 - w_ 0 j).

Lemma alphaE i j : alpha_ i j = 1 - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite /alpha_ mulr_subl mul1r mulr_subr mulr1 -w_split.
by rewrite oppr_sub !addrA addrAC (addrAC 1).
Qed.

Lemma vchar_alpha i j : alpha_ i j \in 'Z[irr W].
Proof. by rewrite mul_vchar // -chi0_1 sub_vchar ?irr_vchar. Qed.

Lemma memc_alpha i j : alpha_ i j \in 'CF(W, V).
Proof.
apply/cfun_onP=> x; rewrite !inE negb_and negbK orbC.
have [Wx /= | /cfun0->//] := boolP (x \in W).
rewrite !cfunE cfun1E Wx /w_ !dprod_IirrE !chi0_1 cfDprod1l cfDprod1r.
rewrite -{3}[x]mul1g -{4}[x]mulg1; case/orP=> [W1x | W2x]; last first.
  rewrite cfDprodEl // lin_char1 ?subrr ?mul0r //.
  exact/char_abelianP/cyclic_abelian.
rewrite mulrC cfDprodEr // lin_char1 ?subrr ?mul0r //.
exact/char_abelianP/cyclic_abelian.
Qed.

Definition beta_ i j : 'CF(G) := 'Ind[G] (alpha_ i j) - 1.

Lemma vchar_beta i j : beta_ i j \in 'Z[irr G].
Proof. by rewrite sub_vchar ?cfInd_vchar ?vchar_alpha // -chi0_1 irr_vchar. Qed.

Lemma cfdot_w i j i' j' :
  '[w_ i j, w_ i' j'] = ((i == i') && (j == j'))%:R.
Proof. by rewrite cfdot_irr inj_eq //; exact: dprod_Iirr_inj. Qed.

Lemma cfdot_alpha i j i' j' : i' != 0 -> j' != 0 ->
  '[alpha_ i j, w_ i' j'] = ((i == i') && (j == j'))%:R.
Proof.
move=> /negbTE Di' /negbTE Dj'; rewrite alphaE -w00 cfdotDl !cfdot_subl.
by rewrite !cfdot_w !(eq_sym 0) Di' Dj' !andbF !subr0 add0r.
Qed.

Lemma cfdot_alpha00 i j : i != 0 -> j != 0 -> '[alpha_ i j, 1] = 1.
Proof.
move=> /negbTE Di /negbTE Dj; rewrite alphaE -w00 cfdotDl !cfdot_subl.
by rewrite !cfdot_w Di Dj !subr0 addr0.
Qed.

Lemma cfnorm_alpha i j : i != 0 -> j != 0 -> '[alpha_ i j] = 4%:R.
Proof.
move=> Di Dj; rewrite {2}alphaE cfdotDr !cfdot_subr cfdot_alpha00 // addrC.
rewrite cfdot_alpha // !addrA -mulrSr alphaE -w00 !(cfdot_subl, cfdotDl).
rewrite !cfdot_w !eqxx !(eq_sym 0) (negbTE Di) (negbTE Dj) !andbF !subr0 !addr0.
by rewrite !add0r !opprK -!mulrSr.
Qed.

Lemma cfdot_Ind_alpha_1 i j : i != 0 -> j != 0 -> 
  '['Ind[G] (alpha_ i j), 1] = 1.
Proof.
move=> Di Dj; have WsG : W \subset G by case: tiW; case.
by rewrite -Frobenius_reciprocity cfRes_cfun1 // cfdot_alpha00.
Qed.

Let VsG : V \subset G^#.
Proof.
apply/subsetP=> g; rewrite !inE negb_or -andbA; case/and3P=> [GniW1 GniW2 GiW].
have WsG : W \subset G by case: tiW; case.
by rewrite (subsetP WsG) // andbT; apply: contra GniW1; move/eqP->; exact: group1.
Qed.

(* This is the first equation of Perterfalvi (3.5.1). *)
Lemma cfdot_beta_1 i j : i != 0 -> j != 0 -> '[beta_ i j, 1] = 0.
Proof.
move=> Di Dj.
by rewrite cfdot_subl cfdot_Ind_alpha_1 // -chi0_1 cfdot_irr subrr.
Qed.

(* These are the other equations of Perterfalvi (3.5.1). *)
Lemma cfdot_beta i j i' j' : i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> 
  '[beta_ i j, beta_ i' j'] =
     ((i == i') * (j == j') + (i == i') + (j == j'))%:R.
Proof.
move=> Di Dj Di' Dj'. 
rewrite cfdot_subr cfdot_beta_1 // subr0.
rewrite cfdot_subl (cfdotC 1) cfdot_Ind_alpha_1 // rmorph1.
have nTi: normedTI (W :\: (W1 :|: W2)) G W by case: tiW.
rewrite (Frobenius_isometry _ nTi) ?memc_alpha //.
rewrite (alphaE i') cfdotDr !cfdot_subr cfdot_alpha00 // addrC -!addrA addKr.
rewrite alphaE -w00 !(cfdot_subl, cfdotDl) !cfdot_w !eqxx !(eq_sym 0) !andbT.
do !rewrite (@negbTE (_ == 0)) ?andbF //; rewrite !oppr_add !oppr0 !opprK.
by rewrite !add0r !addr0 mulnb addrA addrC addrA -!natr_add.
Qed.

Lemma dim_cyclicTIcfun : \dim 'CF(W, V) = (#|Iirr W1|.-1 * #|Iirr W2|.-1)%N.
Proof.
rewrite !card_ord dim_cfun_on_abelian ?(cyclic_abelian, subsetDl) // !NirrE.
have:= cyclic_abelian cyclicW1; rewrite card_classes_abelian => /eqP ->.
have:= cyclic_abelian cyclicW2; rewrite card_classes_abelian => /eqP ->.
apply: (@addnI (#|W1| + #|W2|)%N); rewrite -{1}cardsUI addnAC.
have [_ defW _ ->] := dprodP W1xW2; rewrite cards1.
have /setIidPr <-: (W1 :|: W2) \subset W by rewrite subUset -mulG_subG defW.
rewrite cardsID -(dprod_card W1xW2) -(prednK (cardG_gt0 W1)) /=.
by rewrite addn1 !addSn addnAC -mulnS mulSnr prednK.
Qed.

Definition alpha_base :=
  image (prod_curry alpha_) (setX [set~ ord0] [set~ ord0]).

Lemma alpha_base_free : free alpha_base.
Proof.
apply/freeP=> s s_alpha_0 ij; case def_ij: (enum_val ij) => [i j].
have /andP[Di Dj]: (i != 0) && (j != 0).
  by rewrite -!in_setC1 -in_setX -def_ij enum_valP.
have:= congr1 (cfdotr (w_ i j)) s_alpha_0; rewrite raddf_sum raddf0 => <-.
rewrite (bigD1 ij) //= -tnth_nth tnth_map /tnth -enum_val_nth def_ij.
rewrite cfdotZl cfdot_alpha // !eqxx mulr1 big1 ?addr0 // => kl.
rewrite -tnth_nth tnth_map /tnth -enum_val_nth -(inj_eq enum_val_inj).
case: (enum_val kl) => k l /= => /negbTE ne_kl_ij.
by rewrite cfdotZl cfdot_alpha // -xpair_eqE -def_ij ne_kl_ij mulr0.
Qed.

(* This is Peterfalvi (3.4). *)
Lemma alpha_base_is_basis : is_basis 'CF(W,V) alpha_base.
Proof.
rewrite /is_basis alpha_base_free andbT /is_span -dimv_leqif_eq.
  by rewrite (eqnP alpha_base_free) size_tuple cardsX !cardsC1 dim_cyclicTIcfun.
by rewrite -span_subsetl; apply/allP=> _ /imageP[[i j] _ ->]; exact: memc_alpha.
Qed.

End Proofs.
