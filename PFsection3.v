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

Definition cyclicTIirr i j := 'chi_(dprod_Iirr W1xW2 (i, j)).
Local Notation w_ := cyclicTIirr.

Lemma cTIirr00 : w_ 0 0 = 1.
Proof.
rewrite /w_ dprod_IirrE !chi0_1.
apply/cfun_inP=> x Wx; rewrite cfun1E Wx.
case/(mem_dprod W1xW2): Wx => y [z [W1y W2z -> _]].
by rewrite cfDprodE // !cfun1E W1y W2z mulr1.
Qed.

Lemma cTIirr_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof. by rewrite /w_ !dprod_IirrE !chi0_1 cfDprod1r cfDprod1l. Qed.

Let linearX (i : Iirr W) : lin_char ('chi_i).
Proof.
apply/char_abelianP.
by apply: cyclic_abelian; case: tiW; case.
Qed.

Definition acTIirr i j : 'CF(W) := (1 - w_ i 0) * (1 - w_ 0 j).
Local Notation alpha_ := acTIirr.

Lemma acTIirr1 i j : alpha_ i j 1%g = 0.
Proof.
rewrite !cfunE /cyclicTIirr cfun1Egen group1 (lin_char1 (linearX _)).
by rewrite addrN mul0r.
Qed.

Lemma acTIirrE i j : alpha_ i j = 1 - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite /alpha_ mulr_subl mul1r mulr_subr mulr1 -cTIirr_split.
by rewrite oppr_sub !addrA addrAC (addrAC 1).
Qed.

Lemma vchar_acTIirr i j : alpha_ i j \in 'Z[irr W].
Proof. by rewrite mul_vchar // -chi0_1 sub_vchar ?irr_vchar. Qed.

Lemma memc_acTIirr i j : alpha_ i j \in 'CF(W, V).
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

Definition bcTIirr i j : 'CF(G) := 'Ind[G] (alpha_ i j) - 1.

Local Notation beta_ := bcTIirr.

Lemma vchar_bcTIirr i j : beta_ i j \in 'Z[irr G].
Proof. by rewrite sub_vchar ?cfInd_vchar ?vchar_acTIirr // -chi0_1 irr_vchar. Qed.

Lemma cfdot_cTIirr i j i' j' :
  '[w_ i j, w_ i' j'] = ((i == i') && (j == j'))%:R.
Proof. by rewrite cfdot_irr inj_eq //; exact: dprod_Iirr_inj. Qed.

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
by rewrite (subsetP WsG) // andbT; apply: contra GniW1; move/eqP->; exact: group1.
Qed.

(* This is the first equation of Perterfalvi (3.5.1). *)
Lemma cfdot_bcTIirr_1 i j : i != 0 -> j != 0 -> '[beta_ i j, 1] = 0.
Proof.
move=> Di Dj.
by rewrite cfdot_subl cfdot_Ind_acTIirr_1 // -chi0_1 cfdot_irr subrr.
Qed.

(* These are the other equations of Perterfalvi (3.5.1). *)
Lemma cfdot_bcTIirr i j i' j' : i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> 
  '[beta_ i j, beta_ i' j'] =
     ((i == i') * (j == j') + (i == i') + (j == j'))%:R.
Proof.
move=> Di Dj Di' Dj'. 
rewrite cfdot_subr cfdot_bcTIirr_1 // subr0.
rewrite cfdot_subl (cfdotC 1) cfdot_Ind_acTIirr_1 // rmorph1.
have nTi: normedTI (W :\: (W1 :|: W2)) G W by case: tiW.
rewrite (Frobenius_isometry _ nTi) ?memc_acTIirr //.
rewrite (acTIirrE i') cfdotDr !cfdot_subr cfdot_acTIirr00 //.
rewrite addrC -!addrA addKr acTIirrE -cTIirr00 !(cfdot_subl, cfdotDl).
rewrite !cfdot_cTIirr !eqxx !(eq_sym 0) !andbT.
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
Lemma acTIirr_base_is_basis : is_basis 'CF(W,V) acTIirr_base.
Proof.
rewrite /is_basis acTIirr_base_free andbT /is_span -dimv_leqif_eq.
  by rewrite (eqnP acTIirr_base_free) size_tuple cardsX !cardsC1 
             dim_cyclicTIcfun.
rewrite -span_subsetl; apply/allP=> _ /imageP[[i j] _ ->].
by exact: memc_acTIirr.
Qed.

Definition bcmp (i : Iirr W1) (j : Iirr W2) (v1 v2 v3 : 'CF(G)) :=
 [&& i !=0 , j != 0, orthonormal [::v1;v2;v3],  
   [&& v1 \in 'Z[irr G], v2 \in 'Z[irr G] & v3 \in 'Z[irr G]]
   & beta_ i j == v1 + v2 + v3].

Lemma bcmp_swapl i j v1 v2 v3 : bcmp i j v1 v2 v3 ->  bcmp i j v2 v1 v3.
Proof.
have F1 := (perm_eqlE (perm_catCA [::v1] [::v2] [::v3])).
case/and5P=> V1 V2 V3 B HB; apply/and5P; split=> //.
- by rewrite -(eq_orthonormal F1).
- by rewrite andbA [X in X && _]andbC -andbA.
by rewrite 1?[X in X + _]addrC.
Qed.

Lemma bcmp_swapr i j v1 v2 v3 : bcmp i j v1 v2 v3 -> bcmp i j v1 v3 v2.
Proof.
have F1 := (perm_eqlE (perm_catAC [::v1] [::v2] [::v3])).
case/and5P=> V1 V2 V3 B HB; apply/and5P; split=> //.
- by rewrite -(eq_orthonormal F1).
- by rewrite [X in _ && X]andbC.
by rewrite -?addrA 1?[X in _ + X]addrC ?addrA.
Qed.

Lemma bcmp_rotate i j v1 v2 v3 : bcmp i j v1 v2 v3 ->  bcmp i j v3 v1 v2.
Proof.
have F1 := (perm_eqlE (perm_catCA [::v1 & v2] [::v3] [::])).
case/and5P=> V1 V2 V3 B HB; apply/and5P; split=> //.
- by rewrite -(eq_orthonormal F1).
- by rewrite andbC -andbA.
by rewrite -addrA addrC.
Qed.

Lemma isNatC_exp c n : isNatC c -> isNatC (c ^+ n).
Proof.
move=> Hc; elim: n=> [|n IH]; first by exact: (isNatC_nat 1).
by rewrite exprS isNatC_mul.
Qed.

Lemma isIntC_exp c n : isIntC c -> isIntC (c ^+ n).
Proof.
move=> Hc; elim: n=> [|n IH]; first by exact: (isIntC_nat 1).
by rewrite exprS isIntC_mul.
Qed.

Lemma isNatC_isIntC_even c n : ~~odd n -> isIntC c ->  isNatC (c ^+ n).
Proof.
move=> Heven; rewrite isIntCE=> /orP []; first by exact: isNatC_exp.
rewrite -[n]odd_double_half (negPf Heven) add0n -mul2n exprn_mulr exprS expr1.
by move=> HH; apply: isNatC_exp; rewrite -mulrNN isNatC_mul.
Qed.

Lemma bcmp_exists i j : 
  i != 0 -> j != 0 -> {v | bcmp i j v.1.1 v.1.2 v.2}.
Proof.
move=> Di Dj.
have: '[beta_ i j] = 3%:R by rewrite cfdot_bcTIirr // !eq_refl.
move/(vchar_small_norm (vchar_bcTIirr i j)); case/(_ (eq_refl _))=>
  [] [[|i1 [|i2 [|i3 []]]]] HS //= [H1 H2 H3].
exists (i1, i2, i3); apply/and4P; split=> //=.
rewrite !H2 /in_mem /= ?(eq_refl, orbT, in_cons) //.
by rewrite H3 !big_cons big_nil addr0 addrA.
Qed.

Definition in_bcTIirr i j (v : 'CF(G)) := 
  [&& v \in 'Z[irr G] , '[v] == 1 & '[v, beta_ i j] == 1].

Lemma bcmp_in i j v1 v2 v3 : bcmp i j v1 v2 v3 -> in_bcTIirr i j v1.
Proof.
case/and5P=> Di Dj /orthonormalP /= [] /andP [].
rewrite negb_or orbF => 
    /andP [] /negPf v1Nv2 /negPf v1Nv3 _ Ho /andP [] VCv1 _ HB.
rewrite /in_bcTIirr VCv1 (eqP HB) !raddfD /= !Ho ?(eq_refl,orbT,in_cons) //.
by rewrite v1Nv2 v1Nv3 !addr0 /=.
Qed.

Local Notation "v1 '<> v2" := ((v1 != v2) && (v1 != -v2))%R (at level 10).

Lemma bcmp_diff i j v1 v2 v3 : bcmp i j v1 v2 v3 -> v1 '<> v2.
Proof.
case/and5P=> Di Dj /orthonormalP /= [] /andP [].
rewrite !inE negb_or=> /andP [] /= /negPf v1Dv2 /= _ _ Ho _ _.
rewrite (v1Dv2); apply/eqP=> HH.
have: '[v1, v1] == 1 by rewrite Ho !(eq_refl, inE).
rewrite {2}HH raddfN /= Ho ?(eqxx,orbT,in_cons) // v1Dv2 oppr0.
by rewrite eq_sym oner_eq0.
Qed.

Lemma bcmp_diffs i j v1 v2 v3 : bcmp i j v1 v2 v3 -> 
 [&& v1 '<> v2, v2 '<> v3 & v1 '<> v3].
Proof.
move=> HB.
rewrite (bcmp_diff HB).
rewrite (bcmp_diff (bcmp_swapr HB)).
by rewrite (bcmp_diff (bcmp_swapr (bcmp_swapl HB))).
Qed.

Lemma signC_negb b : (-1) ^+ (negb b) = - ((-1) ^+ b) :> algC.
Proof. by case: b=> //; rewrite opprK. Qed.

Lemma cfdot_virr v1 v2 : 
  v1 \in 'Z[irr G] -> v2 \in 'Z[irr G] -> '[v1] == 1 -> '[v2] == 1 ->
  '[v1,v2] = if (v1 == v2) then 1 else if (v1 == -v2) then -1 else 0.
Proof.
move=> VCv1 VCv2.
move=> /eqP /(vchar_norm1P VCv1) [b1 [i1 ->]].
move=> /eqP /(vchar_norm1P VCv2) [b2 [i2 ->]].
rewrite !cfdotZl !cfdotZr !cfdot_irr !(isIntC_conj, isIntC_sign) //.
rewrite !mulr_sign -scaleNr -signC_negb !eq_signed_irr.
by case: b1; case: b2=> /=; case: (_ == _); rewrite ?(opprK, oppr0).
Qed.

Fact ltC_neq A B : A < B ->  A == B -> false.
Proof.
by move=> AlB AEB; contradict AlB; rewrite (eqP AEB) /ltC eq_refl.
Qed.

Fact ltC_addbr b A B : A < B -> A + (if b then -1 else 0) < B.
Proof.
move=> AlB; case: b; [apply: ltC_trans AlB | by rewrite addr0].
by rewrite -{2}[A]addr0 -oppr0 ltC_add2l ltC_opp -(ltn_ltC 0 1).
Qed.
 

Fact ltC_addbl b A B : A < B -> A < B + (if b then 1 else 0).
Proof.
move=> AlB; case: b; last by rewrite addr0.
apply: ltC_trans AlB _.
by rewrite -{1}[B]addr0 ltC_add2l -(ltn_ltC 0 1).
Qed.

Lemma in_bcTIirrE i j v1 v2 v3 v : 
 bcmp i j v1 v2 v3 -> in_bcTIirr i j v -> [|| v == v1, v == v2 | v == v3].
Proof.
case/and5P=> Di Dj Ho /and3P [] VCv1 VCv2 VCv3 /eqP HB 
             /andP [] VCv /andP [] Nv.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
rewrite HB !raddfD /= cfdot_virr // cfdot_virr // cfdot_virr //.
case: (_ == v1)=> //; case: (_ == v2)=> //; case: (_ == v3)=> //.
rewrite -[X in X + _ + _]add0r; apply: ltC_neq.
repeat apply: ltC_addbr.
by rewrite -(ltn_ltC 0 1).
Qed.

Lemma in_bcTIirr_eq i j v1 v2 v3 v : 
 bcmp i j v1 v2 v3 -> in_bcTIirr i j v = [|| v == v1, v == v2 | v == v3].
Proof.
move=> HB; apply/idP/idP=> HH; first by apply: in_bcTIirrE HB _.
by case/or3P: HH=> /eqP->;
   [ apply: bcmp_in HB | apply: bcmp_in (bcmp_swapl HB) 
                       | apply: bcmp_in (bcmp_rotate HB)].
Qed.

Lemma in_bcTIirr_cmp i j k v1 v2 v3 :
 k != 0 -> bcmp i j v1 v2 v3 -> 
 [|| in_bcTIirr i k v1, in_bcTIirr i k v2 | in_bcTIirr i k v3].
Proof.
case: (boolP (j == k))=> [/eqP -> | Djk Dk].
  by move=> Dk /bcmp_in->.
case/and5P=> Di Dj Ho /and3P [] iV1 iV2 iV3 /eqP HB.
case: (bcmp_exists Di Dk)=> [] [[v4 v5] v6] /= Hbcmp.
rewrite !(in_bcTIirr_eq _ Hbcmp) //.
case/and5P: Hbcmp => _ _ Ho' /and3P [] iV4 iV5 iV6 /eqP HB'.
move: (cfdot_bcTIirr Di Dj Di Dk); rewrite /in_bcTIirr HB HB' eqxx.
rewrite (negPf Djk) mul1n ?(addn0,add0n) /=.
rewrite !cfdotDl !raddfD /=.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv5: '[v5] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv6: '[v6] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
repeat (rewrite cfdot_virr //).
case: (v1 == v4)=> //; case: (v1 == v5)=> //; case: (v1 == v6)=> //.
case: (v2 == v4)=> //; case: (v2 == v5)=> //; case: (v2 == v6)=> //.
case: (v3 == v4)=> //; case: (v3 == v5)=> //; case: (v3 == v6)=> //=.
rewrite !addrA -[X in X + _ + _ + _ + _ + _ + _ + _ + _]add0r.
move/eqP; apply: ltC_neq; repeat apply: ltC_addbr.
by rewrite -(ltn_ltC 0 1).
Qed.

Lemma in_bcTIirr_cmp_sym i j k v1 v2 v3 :
 k != 0 -> bcmp j i v1 v2 v3 -> 
 [|| in_bcTIirr k i v1, in_bcTIirr k i v2 | in_bcTIirr k i v3].
Proof.
case: (boolP (j == k))=> [/eqP -> | Djk Dk].
  by move=> Dk /bcmp_in->.
case/and5P=> Dj Di Ho /and3P [] iV1 iV2 iV3 /eqP HB.
case: (bcmp_exists Dk Di)=> [] [[v4 v5] v6] /= Hbcmp.
rewrite !(in_bcTIirr_eq _ Hbcmp) //.
case/and5P: Hbcmp => _ _ Ho' /and3P [] iV4 iV5 iV6 /eqP HB'.
move: (cfdot_bcTIirr Dj Di Dk Di); rewrite /in_bcTIirr HB HB' eqxx.
rewrite (negPf Djk) ?(addn0,add0n) /=.
rewrite !cfdotDl !raddfD /=.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv5: '[v5] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv6: '[v6] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
repeat (rewrite cfdot_virr //).
case: (v1 == v4)=> //; case: (v1 == v5)=> //; case: (v1 == v6)=> //.
case: (v2 == v4)=> //; case: (v2 == v5)=> //; case: (v2 == v6)=> //.
case: (v3 == v4)=> //; case: (v3 == v5)=> //; case: (v3 == v6)=> //=.
rewrite !addrA -[X in X + _ + _ + _ + _ + _ + _ + _ + _]add0r.
move/eqP; apply: ltC_neq; repeat apply: ltC_addbr.
by rewrite -(ltn_ltC 0 1).
Qed.

Lemma in_bcTIirr_exists i j v : 
  i != 0 -> j != 0 -> in_bcTIirr i j v -> {v1 | bcmp i j v v1.1 v1.2}.
Proof.
move=> NZi NZj Iv.
case: (bcmp_exists NZi NZj)=> [[[v1 v2] v3 /=] HB].
case: (in_bcTIirrE HB Iv); case: (boolP (_ == _))=> [/eqP -> _ | _].
  by exists (v2,v3).
case: (boolP (_ == _))=> [/eqP -> _ | _ /= /eqP ->].
  by exists (v1,v3); apply: bcmp_swapl.
by exists (v1,v2); move: (bcmp_rotate HB).
Qed.

Lemma bcTIirr_false i j k l v1 v2 v3 :
 '[v3] == 1 -> v3 \in 'Z[irr G] ->
  beta_ i j = v1 + v2 + v3 -> beta_ k l = v1 + v2 - v3 -> false.
Proof.
move=> Nv3 VCv3 HB HB'.
have: (2%:R * v3) 1%g = (beta_ i j - beta_ k l) 1%g.
  have->: 2%:R = 1 + 1 :> 'CF(G) by rewrite -(natr_add _ 1 1).
  rewrite mulr_addl !mul1r.
  rewrite HB HB' !oppr_add opprK -oppr_add [v1 + _ + _]addrC.
  by rewrite addrA addrK.
rewrite /bcTIirr [X in _ - X]addrC oppr_add opprK addrA subrK.
rewrite -raddf_sub /= cfInd1 //; last by case: tiW; case.
rewrite 3!cfunE acTIirr1 cfunE acTIirr1 subr0 mulr0.
rewrite cfun1Egen group1 -natr_add.
move/eqP; rewrite mulf_eq0 -(eqN_eqC _ 0) orFb.
case: (vchar_norm1P VCv3 (eqP Nv3))=> b [i1 ->].
by rewrite cfunE mulr_sign; case: b; rewrite ?oppr_eq0 (negPf (irr1_neq0 i1)).
Qed.

Lemma bcmp2_diff i j k v1 v2 v3 v4 v5 : 
 j != k -> bcmp i j v1 v2 v3 -> bcmp i k v1 v4 v5 -> v2 '<> v4.
Proof.
move=> Djk HB HB'.
case/and5P: (HB)=> Di Dj Ho /and3P [] iV1 iV2 iV3 /eqP eHB.
case/and5P: (HB')=> _ Dk Ho' /and3P [] _ iV4 iV5 /eqP eHB'.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv5: '[v5] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
move: (cfdot_bcTIirr Di Dj Di Dk).
rewrite eqxx (negPf Djk) add0n addn0=> HH.
apply/andP; split; apply/negP=> /eqP HH1; rewrite {}HH1 in HB, Ho, eHB.
  suff F: v3 = -v5.
    by rewrite F in eHB; move: (bcTIirr_false Nv5 iV5 eHB' eHB).
  move: HH; rewrite eHB !cfdotDl.
  case/and3P: (bcmp_in HB')=> _ _ /eqP->.
  case/and3P: (bcmp_in (bcmp_swapl HB'))=> _ _ /eqP->.
  rewrite eHB' !raddfD /=.
  case/orthonormalP: Ho=> Hu' HH.
  case/and4P: Hu'; rewrite !inE negb_or=> /andP [] Dv1v4 Dv1v3 Dv4v3 _ _.
  rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv1v3) add0r.
  rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv4v3) add0r.
  rewrite cfdot_virr //; case: (_ == _).
    by move/eqP; rewrite -(natr_add _ 1 1) -(natr_add _ _ 1) -eqN_eqC.
  case: (boolP (_ == _))=> [/eqP //| _].
  by move/eqP; rewrite addr0 -(natr_add _ 1 1) -eqN_eqC.
suff F: v3 = v5.
  move: eHB eHB'.
  rewrite F -!addrA ![_ + v5]addrC !addrA => eHB eHB'.
  by move: (bcTIirr_false Nv4 iV4 eHB' eHB).
move: HH; rewrite eHB !cfdotDl cfdotNl.
case/and3P: (bcmp_in HB')=> _ _ /eqP->.
case/and3P: (bcmp_in (bcmp_swapl HB'))=> _ _ /eqP->.
rewrite eHB' !raddfD /=.
case/orthonormalP: Ho=> Hu' HH.
case/and4P: Hu'; rewrite !inE negb_or=> /andP [] Dv1v4 Dv1v3 Dv4v3 _ _.
rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv1v3) add0r.
rewrite -[v4]opprK cfdotNr.
rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv4v3) oppr0 add0r.
rewrite addrN add0r cfdot_virr //; case: (boolP (_ == _))=> [/eqP //| _].
case: (_ == _)=> /eqP.
  by rewrite eq_sym -subr_eq0 opprK -(natr_add _ 1 1) -(eqN_eqC _ 0).
by rewrite eq_sym oner_eq0.
Qed.

Lemma bcmp2_diffs i j k v1 v2 v3 v4 v5 : 
 j != k -> bcmp i j v1 v2 v3 -> bcmp i k v1 v4 v5 ->
 [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 & v3 '<> v5].
Proof.
move=> Djk HB HB'.
rewrite (bcmp2_diff Djk HB HB').
rewrite (bcmp2_diff Djk HB (bcmp_swapr HB')).
rewrite (bcmp2_diff Djk (bcmp_swapr HB) HB').
by rewrite (bcmp2_diff Djk (bcmp_swapr HB) (bcmp_swapr HB')).
Qed.

Lemma bcmp2_diff_sym i j k v1 v2 v3 v4 v5 : 
 j != k -> bcmp j i v1 v2 v3 -> bcmp k i v1 v4 v5 -> v2 '<> v4.
Proof.
move=> Djk HB HB'.
case/and5P: (HB)=> Dj Di Ho /and3P [] iV1 iV2 iV3 /eqP eHB.
case/and5P: (HB')=> Dk _ Ho' /and3P [] _ iV4 iV5 /eqP eHB'.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv5: '[v5] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
move: (cfdot_bcTIirr Dj Di Dk Di).
rewrite eqxx (negPf Djk) !add0n => HH.
apply/andP; split; apply/negP=> /eqP HH1; rewrite {}HH1 in HB, Ho, eHB.
  suff F: v3 = -v5.
    by rewrite F in eHB; move: (bcTIirr_false Nv5 iV5 eHB' eHB).
  move: HH; rewrite eHB !cfdotDl.
  case/and3P: (bcmp_in HB')=> _ _ /eqP->.
  case/and3P: (bcmp_in (bcmp_swapl HB'))=> _ _ /eqP->.
  rewrite eHB' !raddfD /=.
  case/orthonormalP: Ho=> Hu' HH.
  case/and4P: Hu'; rewrite !inE negb_or=> /andP [] Dv1v4 Dv1v3 Dv4v3 _ _.
  rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv1v3) add0r.
  rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv4v3) add0r.
  rewrite cfdot_virr //; case: (_ == _).
    by move/eqP; rewrite -(natr_add _ 1 1) -(natr_add _ _ 1) -eqN_eqC.
  case: (boolP (_ == _))=> [/eqP //| _].
  by move/eqP; rewrite addr0 -(natr_add _ 1 1) -eqN_eqC.
suff F: v3 = v5.
  move: eHB eHB'.
  rewrite F -!addrA ![_ + v5]addrC !addrA => eHB eHB'.
  by move: (bcTIirr_false Nv4 iV4 eHB' eHB).
move: HH; rewrite eHB !cfdotDl cfdotNl.
case/and3P: (bcmp_in HB')=> _ _ /eqP->.
case/and3P: (bcmp_in (bcmp_swapl HB'))=> _ _ /eqP->.
rewrite eHB' !raddfD /=.
case/orthonormalP: Ho=> Hu' HH.
case/and4P: Hu'; rewrite !inE negb_or=> /andP [] Dv1v4 Dv1v3 Dv4v3 _ _.
rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv1v3) add0r.
rewrite -[v4]opprK cfdotNr.
rewrite HH ?(eqxx, orbT, in_cons) // eq_sym (negPf Dv4v3) oppr0 add0r.
rewrite addrN add0r cfdot_virr //; case: (boolP (_ == _))=> [/eqP //| _].
case: (_ == _)=> /eqP.
  by rewrite eq_sym -subr_eq0 opprK -(natr_add _ 1 1) -(eqN_eqC _ 0).
by rewrite eq_sym oner_eq0.
Qed.

Lemma bcmp2_diffs_sym i j k v1 v2 v3 v4 v5 : 
 j != k -> bcmp j i v1 v2 v3 -> bcmp k i v1 v4 v5 ->
 [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 & v3 '<> v5].
Proof.
move=> Djk HB HB'.
rewrite (bcmp2_diff_sym Djk HB HB').
rewrite (bcmp2_diff_sym Djk HB (bcmp_swapr HB')).
rewrite (bcmp2_diff_sym Djk (bcmp_swapr HB) HB').
by rewrite (bcmp2_diff_sym Djk (bcmp_swapr HB) (bcmp_swapr HB')).
Qed.

Lemma in_bcTIirr_opp i j v : in_bcTIirr j i v -> in_bcTIirr j i (- v) -> false.
Proof.
case/and3P=> _ _ HH; case/and3P=> _ _; rewrite cfdotNl (eqP HH).
by rewrite eq_sym -subr_eq0 opprK -(natr_add _ 1 1) -(eqN_eqC _ 0).
Qed.

Lemma bcmp_in_opp i j k v1 v2 v3 : 
 j != 0 -> bcmp i k v1 v2 v3 ->
   [&& ~~ in_bcTIirr i j (-v1), ~~ in_bcTIirr i j (-v2)
     &  ~~ in_bcTIirr i j (-v3)].
Proof.
move=> NZj HB.
have NZi : i != 0 by case/and3P: HB.
case: (boolP (j == k))=> [/eqP -> | Djk].
  apply/and3P; split; apply/negP=> HH.
  - by have:= in_bcTIirr_opp (bcmp_in HB) HH.
  - by have:= in_bcTIirr_opp (bcmp_in (bcmp_swapl HB)) HH.
  by have:= in_bcTIirr_opp (bcmp_in (bcmp_rotate HB)) HH.
wlog [[v4 v5] HB']: v1 v2 v3 HB / {p | bcmp i j v1 p.1 p.2}.
  case/or3P: (in_bcTIirr_cmp NZj HB)=> HH WL.
  - by apply: WL HB (in_bcTIirr_exists _ _ _).
  - rewrite andbA [X in X && _]andbC -andbA. 
    by apply: WL (bcmp_swapl HB) (in_bcTIirr_exists _ _ _).
  rewrite andbA andbC.
  by apply: WL (bcmp_rotate HB) (in_bcTIirr_exists _ _ _).
apply/and3P; split; apply/negP=> HH.
- by have:= in_bcTIirr_opp (bcmp_in HB') HH.
- case/or3P: (in_bcTIirrE HB' HH)=> /eqP vE.
  - suff F: in_bcTIirr i k (- v1).
      by have:= in_bcTIirr_opp (bcmp_in HB) F.
    by rewrite -vE opprK (bcmp_in (bcmp_swapl HB)).
  - move: (bcmp2_diff Djk HB' HB).
    by rewrite -vE; rewrite eqxx andbF.
  move: (bcmp2_diff Djk (bcmp_swapr HB') HB).
  by rewrite -vE; rewrite eqxx andbF.
case/or3P: (in_bcTIirrE HB' HH)=> /eqP vE.
- suff F: in_bcTIirr i k (- v1).
    by have:= in_bcTIirr_opp (bcmp_in HB) F.
  by rewrite -vE opprK (bcmp_in (bcmp_rotate HB)).
- move: (bcmp2_diff Djk HB' (bcmp_swapr HB)).
  by rewrite -vE eqxx andbF.
move: (bcmp2_diff Djk (bcmp_swapr HB') (bcmp_swapr HB)).
by rewrite -vE; rewrite eqxx andbF.
Qed.

Lemma bcmp_in_opp_sym i j k v1 v2 v3 : 
 j != 0 -> bcmp k i v1 v2 v3 ->
   [&& ~~ in_bcTIirr j i (-v1), ~~ in_bcTIirr j i (-v2)
     &  ~~ in_bcTIirr j i (-v3)].
Proof.
move=> NZj HB.
have NZi : i != 0 by case/and3P: HB.
case: (boolP (j == k))=> [/eqP -> | Djk].
  apply/and3P; split; apply/negP=> HH.
  - by have:= in_bcTIirr_opp (bcmp_in HB) HH.
  - by have:= in_bcTIirr_opp (bcmp_in (bcmp_swapl HB)) HH.
  by have:= in_bcTIirr_opp (bcmp_in (bcmp_rotate HB)) HH.
wlog [[v4 v5] HB']: v1 v2 v3 HB / {p | bcmp j i v1 p.1 p.2}.
  case/or3P: (in_bcTIirr_cmp_sym NZj HB)=> HH WL.
  - by apply: WL HB (in_bcTIirr_exists _ _ _).
  - rewrite andbA [X in X && _]andbC -andbA. 
    by apply: WL (bcmp_swapl HB) (in_bcTIirr_exists _ _ _).
  rewrite andbA andbC.
  by apply: WL (bcmp_rotate HB) (in_bcTIirr_exists _ _ _).
apply/and3P; split; apply/negP=> HH.
- by have:= in_bcTIirr_opp (bcmp_in HB') HH.
- case/or3P: (in_bcTIirrE HB' HH)=> /eqP vE.
  - suff F: in_bcTIirr k i (- v1).
      by have:= in_bcTIirr_opp (bcmp_in HB) F.
    by rewrite -vE opprK (bcmp_in (bcmp_swapl HB)).
  - move: (bcmp2_diff_sym Djk HB' HB).
    by rewrite -vE; rewrite eqxx andbF.
  move: (bcmp2_diff_sym Djk (bcmp_swapr HB') HB).
  by rewrite -vE; rewrite eqxx andbF.
case/or3P: (in_bcTIirrE HB' HH)=> /eqP vE.
- suff F: in_bcTIirr k i (- v1).
    by have:= in_bcTIirr_opp (bcmp_in HB) F.
  by rewrite -vE opprK (bcmp_in (bcmp_rotate HB)).
- move: (bcmp2_diff_sym Djk HB' (bcmp_swapr HB)).
  by rewrite -vE eqxx andbF.
move: (bcmp2_diff_sym Djk (bcmp_swapr HB') (bcmp_swapr HB)).
by rewrite -vE; rewrite eqxx andbF.
Qed.

Lemma bcmp_not_two i1 j1 i2 j2 v1 v2 v3 v4: 
 i1 != i2 -> j1 != j2 ->
 bcmp i1 j1 v1 v2 v3 -> bcmp i2 j2 v1 v2 v4 -> false.
Proof.
move=> Di1i2 Dj1j2 HB HB'.
case/and5P: (HB)=> NZi1 NZj1 Ho /and3P [] VCv1 VCv2 VCv3 EB.
case/and5P: (HB')=> NZi2 NZj2 Ho' /and3P [] _ VCv4 VCv5 EB'.
move: (cfdot_bcTIirr NZi2 NZj2 NZi1 NZj1).
rewrite eq_sym (negPf Di1i2) eq_sym (negPf Dj1j2) !add0n (eqP EB') !cfdotDl.
case/and3P: (bcmp_in HB)=> _ _ /eqP->.
rewrite (eqP EB) !cfdotDr.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
case/orthonormalP: Ho=> /and4P []; rewrite !inE negb_or /and4P.
case/andP=> Iv2 Iv3 Iv23 _ _ HH.
case/orthonormalP: Ho'=> /and4P []; rewrite !inE negb_or /and4P.
case/andP=> _ Iv4 Iv24 _ _ HH'.
rewrite HH' ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv2) add0r.
rewrite HH ?(eqxx, orbT, in_cons) //.
rewrite HH ?(eqxx, orbT, in_cons) // (negPf Iv23) addr0.
rewrite HH' ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv4) add0r.
rewrite HH' ?(eqxx, orbT, in_cons) // eq_sym (negPf Iv24) add0r.
rewrite cfdot_virr //; repeat (case: (_ == _)); move/eqP.
- by rewrite -(natr_add _ 1 1) -(natr_add _  _ 1) -(eqN_eqC _ 0).
- by rewrite addrK -(eqN_eqC 1 0).
by rewrite addr0 -(natr_add _ 1 1) -(eqN_eqC _ 0).
Qed.

Lemma bcmp_two_opp i1 j1 i2 j2 v1 v2 v3 v4: 
 i1 != i2 -> j1 != j2 ->
 bcmp i1 j1 v1 v2 v3 -> bcmp i2 j2 v1 (-v2) v4 -> v3 '<> v4.
Proof.
move=> Di1i2 Dj1j2 HB HB'.
case/and5P: (HB)=> NZi1 NZj1 Ho /and3P [] VCv1 VCv2 VCv3 EB.
case/and5P: (HB')=> NZi2 NZj2 Ho' /and3P [] _ VCv4 VCv5 EB'.
move: (cfdot_bcTIirr NZi2 NZj2 NZi1 NZj1).
rewrite eq_sym (negPf Di1i2) eq_sym (negPf Dj1j2) !add0n (eqP EB') !cfdotDl.
case/and3P: (bcmp_in HB)=> _ _ /eqP->.
rewrite (eqP EB) !cfdotDr !cfdotNl.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
case/orthonormalP: Ho=> /and4P []; rewrite !inE negb_or /and4P.
case/andP=> Iv2 Iv3 Iv23 _ _ HH.
case/orthonormalP: Ho'=> /and4P []; rewrite !inE negb_or /and4P.
case/andP=> _ Iv4 Iv24 _ _ HH'.
rewrite HH ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv2) oppr0 add0r.
rewrite HH ?(eqxx, orbT, in_cons) //.
rewrite HH ?(eqxx, orbT, in_cons) // (negPf Iv23) subr0 addrN add0r.
rewrite HH' ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv4) add0r.
rewrite -[v2]opprK cfdotNr.
rewrite HH' ?(eqxx, orbT, in_cons) // eq_sym (negPf Iv24).
rewrite cfdot_virr //; rewrite ![v3 == _]eq_sym eqr_oppC.
rewrite oppr0 add0r.
repeat (case: (_ == _))=> //; move/eqP.
- by rewrite -(eqN_eqC 1 0).
- by rewrite -(eqN_eqC 1 0).
by rewrite eq_sym -subr_eq0 opprK add0r -(eqN_eqC 1 0).
Qed.

Lemma bcmp_diff_opp i1 j1 i2 j2 v1 v2 v3 v4 v5 : 
 i1 != i2 -> j1 != j2 ->
 bcmp i1 j1 v1 v2 v3 -> bcmp i2 j2 v1 v4 v5 -> 
 [|| (v4 == - v2) && v5 '<> v3 , (v4 == - v3) && v5 '<> v2,
     (v5 == - v2) && v4 '<> v3 | (v5 == - v3) && v4 '<> v2].
Proof.
move=> Di1i2 Dj1j2 HB HB'.
case: (boolP (_ == _))=> /eqP Hv4v2 /=.
  rewrite Hv4v2 in HB'.
  by rewrite 2![v5 == _]eq_sym eqr_oppC (bcmp_two_opp Di1i2 Dj1j2 HB HB').
case: (boolP (_ == _))=> /eqP Hv4v3 /=.
  rewrite Hv4v3 in HB'.
  rewrite 2![v5 == _]eq_sym eqr_oppC.
  by rewrite (bcmp_two_opp Di1i2 Dj1j2 (bcmp_swapr HB) HB').
case: (boolP (_ == _))=> /eqP Hv5v2 /=.
  rewrite Hv5v2 in HB'.
  rewrite [v4 == _]eq_sym.
  by case/andP: (bcmp_two_opp Di1i2 Dj1j2 HB (bcmp_swapr HB'))=> ->.
case: (boolP (_ == _))=> /eqP Hv5v3 /=.
  rewrite Hv5v3 in HB'.
  rewrite [v4 == _]eq_sym.
  by case/andP: (bcmp_two_opp Di1i2 Dj1j2 (bcmp_swapr HB) (bcmp_swapr HB'))=>->.
case/and5P: (HB)=> NZi1 NZj1 Ho /and3P [] VCv1 VCv2 VCv3 EB.
case/and5P: (HB')=> NZi2 NZj2 Ho' /and3P [] _ VCv4 VCv5 EB'.
move: (cfdot_bcTIirr NZi2 NZj2 NZi1 NZj1).
rewrite eq_sym (negPf Di1i2) eq_sym (negPf Dj1j2) !add0n (eqP EB') !cfdotDl.
case/and3P: (bcmp_in HB)=> _ _ /eqP->.
rewrite (eqP EB) !cfdotDr.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv5: '[v5] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
case/orthonormalP: Ho'=> /and4P []; rewrite !inE negb_or /and4P.
case/andP=> Iv4 Iv5 _ _ _ HH.
rewrite HH ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv4) add0r.
rewrite ['[v5,_]]HH ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv5) add0r.
repeat (rewrite cfdot_virr //).
move/eqP: Hv4v2=> /negPf->.
move/eqP: Hv4v3=> /negPf->.
move/eqP: Hv5v2=> /negPf->.
move/eqP: Hv5v3=> /negPf->.
move/eqP; rewrite eq_sym !addrA; apply: ltC_neq.
repeat apply: ltC_addbl.
by rewrite -(ltn_ltC 0 1).
Qed.

Lemma bcmp_opp_diff i1 j1 i2 j2 v1 v2 v3 v4 v5 : 
 i1 != i2 -> j1 != j2 ->
 bcmp i1 j1 v1 v2 v3 ->  bcmp i2 j2 (- v1) v4 v5 -> 
 [|| (v4 == v2) && v5 '<> v3 , (v4 == v3) && v5 '<> v2,
     (v5 == v2) && v4 '<> v3 | (v5 == v3) && v4 '<> v2].
Proof.
move=> Di1i2 Dj1j2 HB HB'.
have HBL := bcmp_swapl HB; have HBR := bcmp_swapr HB.
have HBr := bcmp_rotate HB.
case: (boolP (_ == _))=> /eqP Hv4v2 /=.
  rewrite Hv4v2 in HB'.
  rewrite 2![v5 == _]eq_sym eqr_oppC.
  by rewrite (bcmp_two_opp Di1i2 Dj1j2 HBL (bcmp_swapl HB')).
case: (boolP (_ == _))=> /eqP Hv4v3 /=.
  rewrite Hv4v3 in HB'.
  rewrite 2![v5 == _]eq_sym eqr_oppC.
  by rewrite (bcmp_two_opp Di1i2 Dj1j2 HBr (bcmp_swapl HB')).
case: (boolP (_ == _))=> /eqP Hv5v2 /=.
  rewrite Hv5v2 in HB'.
  rewrite 2![v4 == _]eq_sym eqr_oppC.
  by case/andP: (bcmp_two_opp Di1i2 Dj1j2 HBL (bcmp_rotate HB'))=> _ ->.
case: (boolP (_ == _))=> /eqP Hv5v3 /=.
  rewrite Hv5v3 in HB'.
  rewrite [v4 == _]eq_sym eqr_oppC.
  by case/andP: (bcmp_two_opp Di1i2 Dj1j2 HBr (bcmp_rotate HB'))=> _ ->.
case/and5P: (HB)=> NZi1 NZj1 Ho /and3P [] VCv1 VCv2 VCv3 EB.
case/and5P: (HB')=> NZi2 NZj2 Ho' /and3P [] _ VCv4 VCv5 EB'.
move: (cfdot_bcTIirr NZi2 NZj2 NZi1 NZj1).
rewrite eq_sym (negPf Di1i2) eq_sym (negPf Dj1j2) !add0n (eqP EB') !cfdotDl.
rewrite cfdotNl; case/and3P: (bcmp_in HB)=> _ _ /eqP->.
rewrite (eqP EB) !cfdotDr.
have Nv1: '[v1] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv2: '[v2] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv3: '[v3] == 1.
  by case/orthonormalP: Ho=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv4: '[v4] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
have Nv5: '[v5] == 1.
  by case/orthonormalP: Ho'=> _ ->; rewrite !(eqxx,orbT,in_cons).
case/orthonormalP: Ho'=> /and4P []; rewrite !inE negb_or /and4P.
case/andP=> Iv4 Iv5 _ _ _ HH.
rewrite -[v1]opprK cfdotNr.
rewrite HH ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv4) oppr0 add0r.
rewrite cfdotNr ['[v5,_]]HH ?(eqxx, orbT, in_cons) //  eq_sym (negPf Iv5).
rewrite oppr0 add0r.
repeat (rewrite cfdot_virr //).
move/eqP: Hv4v2=> /negPf->.
move/eqP: Hv4v3=> /negPf->.
move/eqP: Hv5v2=> /negPf->.
move/eqP: Hv5v3=> /negPf->.
move/eqP; rewrite !addrA; apply: ltC_neq.
repeat apply: ltC_addbr.
by rewrite ltC_sub opprK add0r -(ltn_ltC 0 1).
Qed.

Section Main.

Let R := 'CF(G).

Variable m n p : nat.

Variable cmpR : 'I_m.-1.+1 -> 'I_n.-1.+1 -> R -> R -> R -> bool.

Variable inR : 'I_m.-1.+1 -> 'I_n.-1.+1 -> R -> bool.

Local Notation "v1 '<> v2" := ((v1 != v2) && (v1 != -v2))%R (at level 10).

Hypothesis Oddm : odd m.

Hypothesis H2Lm : (2 < m)%N.

Hypothesis H2Ln : (2 < n)%N.

Hypothesis cmpR_swapl :
 forall i j v1 v2 v3, cmpR i j v1 v2 v3 ->  cmpR i j v2 v1 v3.

Hypothesis cmpR_swapr :
  forall i j v1 v2 v3, cmpR i j v1 v2 v3 -> cmpR i j v1 v3 v2.

Hypothesis cmpR_rotate :
  forall i j v1 v2 v3,  cmpR i j v1 v2 v3 ->  cmpR i j v3 v1 v2.

Hypothesis cmpR0 : forall i  j, i != 0 -> j != 0 ->
  {v | cmpR i j v.1.1 v.1.2 v.2}.

Hypothesis cmpR0F : forall i j k, i != 0 -> j != 0 -> inR i j k ->
  { v | cmpR i j k v.1 v.2}.

Hypothesis cmpR1 : forall i j v1 v2 v3, 
 cmpR i j v1 v2 v3 -> inR i j v1.

Hypothesis cmpR2 : forall i j v1 v2 v3, 
 cmpR i j v1 v2 v3 -> [&& v1 '<> v2, v2 '<> v3 & v1 '<> v3].

Hypothesis cmpR3 : forall i j v1 v2 v3 v, 
 cmpR i j v1 v2 v3 -> inR i j v -> [|| v == v1, v == v2 | v == v3].

Hypothesis cmpR4 : forall i j k v1 v2 v3 v4 v5, 
 j != k -> cmpR i j v1 v2 v3 -> cmpR i k v1 v4 v5 -> 
  [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 & v3 '<> v5].

Hypothesis cmpR4b : forall i j k v1 v2 v3 v4 v5,
 j != k ->  cmpR j i v1 v2 v3 -> cmpR k i v1 v4 v5 ->
  [&& v2 '<> v4, v2 '<> v5, v3 '<> v4 &  v3 '<> v5].

Hypothesis cmpR5 : forall i j k v1 v2 v3, 
 k != 0 -> cmpR i j v1 v2 v3 -> [|| inR i k v1, inR i k v2 | inR i k v3].

Hypothesis cmpR5b : forall i j k v1 v2 v3, 
 k != 0 -> cmpR j i v1 v2 v3 -> [|| inR k i v1, inR k i v2 | inR k i v3].

Hypothesis cmpR6 : forall i1 j1 i2 j2 v1 v2 v3 v4 v5, 
 i1 != i2 -> j1 != j2 -> cmpR i1 j1 v1 v2 v3 -> cmpR i2 j2 v1 v4 v5 -> 
 [|| (v4 == - v2) && v5 '<> v3, (v4 == - v3) && v5 '<> v2,
     (v5 == - v2) && v4 '<> v3 | (v5 == - v3) && v4 '<> v2].

Hypothesis cmpR6b : forall i1 j1 i2 j2 v1 v2 v3 v4 v5, 
  i1 != i2 -> j1 != j2 -> cmpR i1 j1 v1 v2 v3 -> cmpR i2 j2 (- v1) v4 v5 -> 
 [|| (v4 == v2) && v5 '<> v3, (v4 == v3) && v5 '<> v2,
     (v5 == v2) && v4 '<> v3 | (v5 == v3) && v4 '<> v2].

Hypothesis cmpR7 : forall i j k v1 v2 v3, 
 j != 0 -> cmpR k i v1 v2 v3 ->
 [&& ~~ inR j i (-v1), ~~ inR j i (-v2) & ~~ inR j i (-v3)].

Hypothesis cmpR7b : forall i j k v1 v2 v3, 
  j != 0 -> cmpR i k v1 v2 v3 ->
   [&& ~~ inR i j (-v1), ~~ inR i j (-v2) &  ~~ inR i j (-v3)].

Fact cmpR3F: forall i1 i2 j v1 v2 v3 v4 v5, 
   i1 != i2 -> cmpR i1 j v1 v2 v3 -> cmpR i2 j v1 v4 v5 -> 
   ~~ inR i2 j v2.
Proof.
move=> i1 i2 j v1 v2 v3 v4 v5 Di1i2 Bi1j Bi2j; apply/negP.
move/(cmpR3 Bi2j)=> /or3P [] /eqP HH; 
    try (rewrite HH in Bi1j) ; try (rewrite HH in Bi2j).
- by case: (cmpR2 Bi1j); rewrite eq_refl.
- by move: (cmpR4b Di1i2 Bi1j Bi2j); rewrite eq_refl.
by move: (cmpR4b Di1i2 Bi1j Bi2j); rewrite eq_refl andbF.
Qed.

Lemma main_aux : 
  forall i1 i2 i3 i4 j j' 
         x1 x2 x3 x4 x5 x6 x7,
 i1 != 0 -> j' != 0 -> j' != j ->
 i4 != i3 -> i4 != i2 -> i4 != i1 -> i3 != i2 -> i3 != i1 -> i2 != i1 -> 
 cmpR i1 j x1 x2 x3 -> cmpR i2 j x1 x4 x5 ->
 cmpR i3 j x2 x4 x6 -> cmpR i4 j x1 x6 x7 ->
 inR i1 j' x1 -> cmpR i1 j' x1 (-x5) (-x7).
Proof.
move=> i1 i2 i3 i4 j j' x1 x2 x3 x4 x5 x6 x7 NZi1 NZj' Dj'j
       Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1 Bi1j Bi2j Bi3j Bi4j.
case/(cmpR0F NZi1 NZj')=> [[x x'] /= Bi1j'].
have Djj' : j != j' by rewrite eq_sym.
wlog: x x' x1 x4 x5  Bi1j Bi2j Bi3j Bi4j Bi1j' 
  / x == - x4 \/ x == - x5 => [WL|].
  case/or4P: (cmpR6 Di2i1 Djj' Bi2j Bi1j')=> /andP [] x'E d'E.
  - by apply: WL Bi1j Bi2j Bi3j Bi4j Bi1j' _; left.
  - by apply: WL Bi1j Bi2j Bi3j Bi4j Bi1j' _; right.
  - by apply: WL Bi1j Bi2j Bi3j Bi4j (cmpR_swapr Bi1j') _; left.
  by apply: WL Bi1j Bi2j Bi3j Bi4j (cmpR_swapr Bi1j') _; right.
case=> xE; rewrite {x xE}(eqP xE) in Bi1j'.
  case/or4P: (cmpR6b Di3i1 Djj' (cmpR_swapl Bi3j) (cmpR_swapl Bi1j'))
          => /andP [] xE dE.
  - by case/and3P: (cmpR2 Bi1j); rewrite (eqP xE) eq_refl.
  - by case/and3P: (cmpR2 Bi4j); rewrite (eqP xE) eq_refl.
  - rewrite (eqP xE) in Bi1j'.
    by case/and4P: (cmpR4 Djj' Bi1j Bi1j'); rewrite eq_refl.
  rewrite (eqP xE) in Bi1j'.
  case/or4P: (cmpR6 Di4i1 Djj' Bi4j Bi1j')=> /andP [] x''E d''E.
  - rewrite eqr_opp in x''E; case/and3P: (cmpR2 (cmpR_rotate Bi1j')).
    by rewrite (eqP x''E) opprK eq_refl andbF.
  - by case/andP: d''E; rewrite eq_refl.
  - case/and3P: (cmpR7 NZi1 Bi1j').
    rewrite -(eqP x''E)=> _ _ /negP [].
    by apply: cmpR1 (cmpR_rotate Bi1j').
  by case/and3P: (cmpR2 Bi4j); rewrite (eqP x''E) eq_refl andbF.
case/or4P: (cmpR6 Di4i1 Djj' Bi4j Bi1j')=> /andP [] xE dE.
- case/and4P: (cmpR4b Di3i2 (cmpR_swapl Bi3j) (cmpR_swapl Bi2j)).
  by rewrite eqr_opp in xE; rewrite (eqP xE) eq_refl.
- case/and4P: (cmpR4b Di4i2 Bi4j Bi2j).
  by rewrite eqr_opp in xE; rewrite (eqP xE) eq_refl.
- rewrite (eqP xE) in Bi1j'.
  case/or4P: (cmpR6b Di3i1 Djj' (cmpR_rotate Bi3j) (cmpR_rotate Bi1j'))
        => /andP [] x'E d'E.
  - by case/and3P: (cmpR2 Bi1j); rewrite (eqP x'E) eq_refl.
  - by case/and3P: (cmpR2 Bi2j); rewrite (eqP x'E) eq_refl.
  - case/and3P: (cmpR7 NZi1 Bi2j).
    by rewrite (eqP x'E) (cmpR1 (cmpR_swapl Bi1j)).
  by case/and3P: (cmpR2 Bi2j); rewrite -(eqP x'E) eq_refl andbF.
by rewrite (eqP xE) in Bi1j'.
Qed.

(* This is almost 3.5.5 *)
Lemma main : forall j, 
  {x | if (j == 0) then x = 0 else forall i, i != 0 -> inR i j x}.
Proof.
move=> j; case: (boolP (j == 0))=> [Zj | NZj]; first by exists 0.
pose i1 : 'I_m.-1.+1 := inZp 1.
pose i2 : 'I_m.-1.+1 := inZp 2.
have NZi1 : i1 != 0 :> 'I_m.-1.+1.
  apply/eqP; move/val_eqP=> /=.
  rewrite modn_small //.
  by case: m H2Lm=> // [] // [].
have NZi2 : i2 != 0.
  apply/eqP; move/val_eqP=> /=.
  rewrite modn_small //.
  by case: m H2Lm=> // [] // [] // [].
have Di2i1 : i2 != i1.
  apply/eqP; move/val_eqP=> /=.
  by rewrite !modn_small //;
     case: m H2Lm=> // [] // [] // [] // [].
move: H2Lm; rewrite leq_eqVlt; case: (boolP (_ == _))=> [/eqP H3Em _ | _ /=].
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
  case: (cmpR0 NZi1 NZj)=> [[[v1 v2] v3] /=  Bi1j].
  case: (cmpR5b NZi2 Bi1j).
  case: (boolP (inR _ _ _))=> [HH _ | _].
    by exists v1; apply: F (cmpR1 Bi1j) _.
  case: (boolP (inR _ _ _))=> [HH _ | _ /= HH].
    by exists v2; apply: F (cmpR1 (cmpR_swapl Bi1j)) _.
  by exists v3; apply: F (cmpR1 (cmpR_rotate Bi1j)) _.
rewrite leq_eqVlt; case: (boolP (_ == _))=> [/eqP HH|_ /= H4Lm].
  by contradict Oddm; rewrite -HH.
case: (cmpR0 NZi1 NZj)=> [] [[x1 x2] x3 /= Bi1j].
wlog:  x1 x2 x3 Bi1j / inR i2 j x1 => [WL | x1Ii2].
  move: (cmpR5b NZi2 Bi1j).
  case: (boolP (inR _ _ _))=> [xIi2 _ | _]; first by apply: WL Bi1j xIi2.
  case: (boolP (inR _ _ _))=> [xIi2 _ | /= _ xIi2].
    by apply: WL (cmpR_swapl Bi1j) xIi2.
  by apply: WL (cmpR_rotate Bi1j) xIi2.
case: (cmpR0F NZi2 NZj x1Ii2)=> {x1Ii2}[] [x4 x5] /= Bi2j.
case: (boolP (forallb i , (i != 0) ==> inR i j x1))=> [/forallP HH|].
  by exists x1=> // i NZi; move/implyP: (HH i); move/(_ NZi).  
rewrite negb_forall; move/existsP=> HH; suff: false by [].
case: HH=> i3; rewrite negb_imply; case/andP=> NZi3 x3NIi3.
have Di3i1: i3 != i1.
  by apply: contra x3NIi3; move/eqP->; move: (cmpR1 Bi1j).
have Di3i2: i3 != i2.
  by apply: contra x3NIi3; move/eqP->; move: (cmpR1 Bi2j).
wlog:  x2 x3 Bi1j / inR i3 j x2 => [WL | x2Ii3].
  case/or3P: (cmpR5b NZi3 Bi1j)=> xIi3; first by case/negP: x3NIi3.
    by apply: WL Bi1j xIi3.
  by apply: WL (cmpR_swapr Bi1j) xIi3.
case: (cmpR0F NZi3 NZj x2Ii3)=> {x2Ii3}[] [x' x6] /= Bi3j.
wlog: x' x4 x5 x6 Bi2j Bi3j / (x4 == x')=> WL.
  case/or3P: (cmpR5b NZi3 Bi2j)=> x4Ii3; first by case/negP: x3NIi3.
    case/or3P: (cmpR3 Bi3j x4Ii3)=> x4E.
    - by case/and4P: (cmpR4b Di2i1 Bi2j Bi1j); rewrite (eqP x4E) eq_refl.
    - by apply: WL Bi2j Bi3j x4E.
    by apply: WL Bi2j (cmpR_swapr Bi3j) x4E.
  case/or3P: (cmpR3 Bi3j x4Ii3)=> x5E.
  - case/and4P: (cmpR4b Di2i1 (cmpR_swapr Bi2j) Bi1j).
    by rewrite (eqP x5E) eq_refl=> /negP [].
  - by apply: WL (cmpR_swapr Bi2j) Bi3j x5E.
  by apply: WL (cmpR_swapr Bi2j) (cmpR_swapr Bi3j) x5E.
rewrite -(eqP WL) {x' WL} in Bi3j.
have: (4 < #|'I_m.-1.+1|)%N.
  by case: m H4Lm=> //= m1; rewrite card_ord.
rewrite (cardD1 (0: 'I__)) (cardD1 i1) (cardD1 i2) (cardD1 i3) !inE ?eq_refl.
rewrite NZi1 NZi2 Di2i1 NZi3 Di3i1 Di3i2 !add1n !ltnS.
case/card_gt0P=> i4; rewrite !inE=> /and5P [] Di4i3 Di4i2 Di4i1 NZi4 _.
case: (cmpR0 NZi4 NZj)=> [] [[x x'] x7] /= Bi4j.
wlog: x x' x1 x2 x3 x4 x5 x6 x7 i1 i2 i3 i4
      NZi1 NZi2 NZi3 {x3NIi3}NZi4 Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1 
      Bi1j Bi2j Bi3j Bi4j /
   ((x1 == x /\ x6 == x') \/ 
    [/\ x == x3, x' == x5 & x7 == x6])=> [WL |].
 case: (boolP (inR i4 j x3))=> [x3Ii4 | x3NIi4].
    wlog: x x' x7 Bi4j / x = x3 => [WL1|x3E].
      case/or3P: (cmpR3 Bi4j x3Ii4)=> /eqP x3E; first by apply: WL1 Bi4j _.
        by apply: WL1 (cmpR_swapl Bi4j) _.
      by apply: WL1 (cmpR_rotate Bi4j) _.
    have x1NIi4: ~~(inR i4 j x1).
      apply/negP=> x1Ii4; rewrite x3E in Bi4j.
      case/or3P: (cmpR3 Bi4j x1Ii4)=> x4E.
      - by case/and3P: (cmpR2 Bi1j)=> _ _ /andP [] /negP.
      - case/and4P: (cmpR4b Di4i1 Bi4j (cmpR_rotate Bi1j)).
        by rewrite (eqP x4E) eq_refl.
      case/and4P: (cmpR4b Di4i1 Bi4j (cmpR_rotate Bi1j)).
      by rewrite (eqP x4E) eq_refl.
    case: (boolP (inR i4 j x4))=> [x4Ii4 | x4NIi4].
      wlog: x' x7 Bi4j / x' = x4 => [WL1 | x'E].
        case/or3P: (cmpR3 Bi4j x4Ii4)=> /eqP x4E.
        - case/and4P: (cmpR4b Di2i1 Bi2j Bi1j)=> //.
          by rewrite -x3E x4E eq_refl.
        - by apply: WL1 Bi4j _.
        by apply: WL1 (cmpR_swapr Bi4j) _.
      move: {Bi1j}(cmpR_swapl Bi1j)=> Bi1j.
      move: {Bi3j}(cmpR_swapl Bi3j)=> Bi3j.
      move: {Bi4j}(cmpR_swapl Bi4j)=> Bi4j.
      have x4Ni1: ~~ inR i1 j x4.
        have Di1i2 : i1 != i2 by rewrite eq_sym.
        case/and4P: (cmpR4b Di2i1 Bi2j (cmpR_swapl Bi1j))=> 
           /andP [] Hv1 _ /andP [] Hv2 _ _ _.
        apply/negP=> x4Ii1.
        case/or3P: (cmpR3 (cmpR_swapl Bi1j) x4Ii1)=> x4E; 
            [| case/negP: Hv1 | case/negP: Hv2]=> //.
        case/and3P: (cmpR2 Bi1j)=> /andP [] /negP []; rewrite eq_sym. 
        by case/negP: x1NIi4; rewrite -(eqP x4E).
      apply: WL Bi3j (cmpR_swapl Bi2j) Bi1j Bi4j _; rewrite // eq_sym //.
      by left; split; apply /eqP.
    wlog: x' x7 Bi4j / x' = x5=> [WL1|].
      case/or3P: (cmpR5b NZi4 Bi2j)=> xIi4; first by case/negP: x1NIi4.
        by case/negP: x4NIi4.
      case/or3P: (cmpR3 Bi4j xIi4)=> /eqP xE.
      - have Di1i2 : i1 != i2 by rewrite eq_sym.
        case/and4P: (cmpR4b Di1i2 Bi1j Bi2j)=> _ _ _.
        by rewrite xE -x3E eq_refl.
      - by apply: WL1 Bi4j _.
      by apply: WL1 (cmpR_swapr Bi4j) _.
    move=> x'E.
    apply: WL (Bi1j) (Bi2j) (Bi3j) (Bi4j) _ => //; 
       right; split; apply/eqP => //.
    rewrite x3E x'E in Bi4j.  
    case/or3P: (cmpR5b NZi4 Bi3j)=> xIi4.
    - case/and4P: (cmpR4b Di4i1 Bi4j (cmpR_rotate Bi1j)).
      by case/or3P: (cmpR3 Bi4j xIi4)=> /eqP xE;
         first case: (cmpR2 (cmpR_rotate Bi1j))=> /and3P [] _ _ /andP [];
         rewrite xE eq_refl.
    - by case/negP: x4NIi4.
    case/or3P: (cmpR3 Bi4j xIi4)=> /eqP xE //.
      case/and4P: (cmpR4b Di3i1 Bi3j (cmpR_swapl Bi1j)) => _ _ _.
      by rewrite xE -x3E eq_refl.
    case/and4P: (cmpR4b Di3i2 (cmpR_swapl Bi3j) (cmpR_swapl Bi2j))=> _ _ _.
    by rewrite xE eq_refl.
  wlog: x x' x7 x1 x2 x3 x4 x5 x6 i1 i2 i3 
        NZi1 NZi2 NZi3 Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1
       {x3NIi4 x3NIi3}Bi1j Bi2j Bi3j Bi4j
       / x == x1 => [WL1|].
    case/or3P: (cmpR5b NZi4 Bi1j)=> xIi4; last by case/negP: x3NIi4.
      case/or3P: (cmpR3 Bi4j xIi4)=> /eqP xE //.
      - by apply: WL1 Bi1j Bi2j Bi3j Bi4j _ => //; rewrite xE eq_refl.
      - by apply: WL1 Bi1j Bi2j Bi3j (cmpR_swapl Bi4j) _ 
               => //; rewrite xE eq_refl.
      by apply: WL1 Bi1j Bi2j Bi3j (cmpR_rotate Bi4j) _ 
               => //; rewrite xE eq_refl.
    case/or3P: (cmpR3 Bi4j xIi4)=> /eqP xE //.
    - by apply: WL1 (cmpR_swapl Bi1j) Bi3j Bi2j Bi4j _; 
         rewrite // eq_sym // xE.
    - by apply: WL1 (cmpR_swapl Bi1j) Bi3j Bi2j (cmpR_swapl Bi4j) _; 
         rewrite // eq_sym // xE.
    by apply: WL1 (cmpR_swapl Bi1j) Bi3j Bi2j (cmpR_rotate Bi4j) _; 
         rewrite // eq_sym // xE.
  move/eqP=> xE.
  wlog: x' x7 Bi4j / x' == x6 => [WL1 | x'E].
    case/or3P: (cmpR5b NZi4 Bi3j)=> xIi4.
    - rewrite xE in Bi4j; have Di1i4 : i1 != i4 by rewrite eq_sym.
      by case/negP: (cmpR3F Di1i4 Bi1j Bi4j).
    - rewrite xE in Bi4j; have Di2i4 : i2 != i4 by rewrite eq_sym.
      by case/negP: (cmpR3F Di2i4 Bi2j Bi4j).
    case/or3P: (cmpR3 Bi4j xIi4)=> /eqP x6E //.
    - rewrite x6E xE in Bi3j.
      case/and4P: (cmpR4b Di3i1 (cmpR_rotate Bi3j) Bi1j).
      by rewrite eq_refl.
    - by apply: WL1 Bi4j _; rewrite x6E eq_refl.
    by apply: WL1 (cmpR_swapr Bi4j) _; rewrite x6E eq_refl.
  by apply: WL Bi1j Bi2j Bi3j Bi4j _ => //; left; split;
    rewrite ?xE ?(eqP x'E) eq_refl.
have [j'[NZj' Dj'j]]: exists j', j' != 0 /\ j'!= j.
  pose j1 : 'I_n.-1.+1 := inZp 1.
  pose j2 : 'I_n.-1.+1 := inZp 2.
  have NZj1 : j1 != 0 :> 'I_n.-1.+1.
    apply/eqP; move/val_eqP=> /=.
    rewrite modn_small //.
    by case: n H2Ln=> // [] // [].
  have NZj2 : j2 != 0.
    apply/eqP; move/val_eqP=> /=.
    by rewrite modn_small //; case: n H2Ln => // [] // [] // [].
  have Dj2j1 : j2 != j1.
    apply/eqP; move/val_eqP=> /=.
    by rewrite !modn_small //; case: n H2Ln => // [] // [] // [] // [].
  exists (if j == j1 then j2 else j1).
  by case: (boolP (j == j1))=> [/eqP -> |]; split=> //; rewrite eq_sym. 
case=> [[xE x'E] | [xE x'E x7E]]; last first.
  (* This PF 3.5.4.6 *)
  rewrite (eqP xE) (eqP x'E) {xE x'E x7E}(eqP x7E) in Bi4j.
  wlog: i1 i2 i3 i4 x1 x2 x3 x4 x5 x6
        NZi4 NZi3 NZi2 NZi1 Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1 
        Bi1j Bi2j Bi3j Bi4j / inR i1 j' x1 => [WL | x1Ii1].
    case/or3P: (cmpR5 NZj' Bi1j)=> xIi1.
    - by apply: WL Bi1j Bi2j Bi3j Bi4j _.
    - by apply: WL (cmpR_swapl Bi1j) Bi3j Bi2j (cmpR_swapr Bi4j) _;
         rewrite // eq_sym.
    by apply: WL (cmpR_rotate Bi1j) Bi4j (cmpR_swapr Bi2j) (cmpR_swapr Bi3j) _;
       rewrite // eq_sym.
  case: (cmpR0F NZi1 NZj' x1Ii1)=> {x x' x1Ii1}[] [x x'] /= Bi1j'.
  wlog: i1 i2 i3 i4 x x' x1 x2 x3 x4 x5 x6 
        NZi4 NZi3 NZi2 NZi1 Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1 
        Bi1j Bi2j Bi3j Bi4j Bi1j' / x == - x4 => [WL | x'E].
    have Djj' : j != j' by rewrite eq_sym.
    case/or4P: (cmpR6 Di2i1 Djj' Bi2j Bi1j')=> /andP [] xE dE. 
    - by apply: WL Bi1j Bi2j Bi3j Bi4j Bi1j' _.
    - by apply: WL (cmpR_swapr Bi1j) (cmpR_swapr Bi2j) Bi4j Bi3j Bi1j' _;
         rewrite // eq_sym.
    - by apply: WL Bi1j Bi2j Bi3j Bi4j (cmpR_swapr Bi1j') _.
    by apply: WL (cmpR_swapr Bi1j) (cmpR_swapr Bi2j) Bi4j Bi3j 
                 (cmpR_swapr Bi1j')_; rewrite // eq_sym.
  rewrite {x'E}(eqP x'E) in Bi1j'.
  move: {Bi1j'}(cmpR_swapl Bi1j')=> Bi1j'.
  move: {Bi3j}(cmpR_swapl Bi3j)=> Bi3j.
  have Djj' : j != j' by rewrite eq_sym.
  case/or4P: (cmpR6b Di3i1 Djj' Bi3j Bi1j')=> /andP [] xE dE.
  - by case/and3P: (cmpR2 Bi1j); rewrite (eqP xE) eq_refl.
  - rewrite (eqP xE) in Bi1j.
    by case/and4P: (cmpR4b Di3i1 (cmpR_rotate Bi3j) Bi1j); rewrite eq_refl.
  - rewrite (eqP xE) in Bi1j'.
    by case/and4P: (cmpR4 Djj' Bi1j (cmpR_swapl Bi1j')); rewrite eq_refl.
  rewrite (eqP xE) in Bi1j'.
  move: {Bi1j'}(cmpR_rotate Bi1j')=> Bi1j'.
  move: {Bi4j}(cmpR_rotate Bi4j)=> Bi4j.
  case/or4P: (cmpR6 Di4i1 Djj' Bi4j Bi1j')=> /andP [] x'E d'E.
  - rewrite eqr_opp in x'E.
    case/and4P: (cmpR4b Di2i1 Bi2j Bi1j).
    by rewrite (eqP x'E) eq_refl.
  - rewrite eqr_opp in x'E.
    by case/and3P: (cmpR2 Bi2j); rewrite (eqP x'E) eq_refl.
  - by case/and3P: (cmpR2 Bi1j); rewrite -(eqP x'E) eq_refl andbF.
  by case/and3P: (cmpR2 Bi2j); rewrite -(eqP x'E) eq_refl andbF.
rewrite -(eqP xE) -{x x' xE x'E}(eqP x'E) in Bi4j.
(* This is 3.5.4.1 *)
have F1: inR i1 j' x1 -> cmpR i1 j' x1 (-x5) (-x7).
  by apply: main_aux Bi1j Bi2j Bi3j Bi4j.
have F2: inR i2 j' x1 -> cmpR i2 j' x1 (-x3) (-x7).
  by rewrite eq_sym in Di2i1; apply: main_aux Bi2j Bi1j (cmpR_swapl Bi3j) Bi4j.
have F3: inR i4 j' x1 -> cmpR i4 j' x1 (-x3) (-x5).
  by apply: main_aux Bi4j Bi1j (cmpR_rotate Bi3j) Bi2j; rewrite // eq_sym.
(* This is 3.5.4.2 *)
wlog: i1 i2 i4 x2 x3 x4 x5 x6 x7
      NZi4 NZi2 NZi1 Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1 F1 F2 F3
      Bi1j Bi2j Bi3j Bi4j / inR i3 j' x2 => [WL|].
  case/or3P: (cmpR5 NZj' Bi3j).
  - by apply: WL Bi1j Bi2j Bi3j Bi4j.
  - by apply: WL Bi2j Bi1j (cmpR_swapl Bi3j) Bi4j; 
       rewrite // 1?eq_sym => // HH; apply: cmpR_swapr; apply: F3.
  apply: WL Bi4j Bi2j (cmpR_swapr (cmpR_rotate Bi3j)) Bi1j; 
       rewrite // 1?eq_sym=> // HH.
  - by apply: cmpR_swapr; apply: F3.
  - by apply: cmpR_swapr; apply: F2.
  by apply: cmpR_swapr; apply: F1.
case/(cmpR0F NZi3 NZj')=> [] [x x8] /= Bi3j'.
move: {Bi1j} (cmpR_swapl Bi1j)=> Bi1j.
wlog: x x8 x1 x2 x3 F1 F2 F3 Bi1j Bi2j Bi3j Bi4j Bi3j' 
          / x == - x1 \/ x == - x3 => [WL|].
  case/or4P: (cmpR6 Di3i1 Dj'j Bi3j' Bi1j)=> /andP [] x'E d'E.
  - apply: WL Bi1j Bi2j Bi3j Bi4j Bi3j' _=> //.
    by rewrite (eqP x'E) opprK eq_refl; left.
  - apply: WL Bi1j Bi2j Bi3j Bi4j (cmpR_swapr Bi3j') _=> //. 
    by rewrite (eqP x'E) opprK eq_refl; left.
  - apply: WL Bi1j Bi2j Bi3j Bi4j Bi3j' _ => //.
    by rewrite (eqP x'E) opprK eq_refl; right.
  apply: WL Bi1j Bi2j Bi3j Bi4j (cmpR_swapr Bi3j')  _ => //.
  by rewrite // (eqP x'E) opprK eq_refl; right.
move: {Bi1j} (cmpR_swapl Bi1j)=> Bi1j.
case=> /eqP HH; rewrite {x}HH in Bi3j'.
  move: {Bi3j'} (cmpR_swapl Bi3j')=> Bi3j'.
  have Di2i3 : i2 != i3 by rewrite eq_sym.
  have Djj' : j != j' by rewrite eq_sym.
  case/or4P: (cmpR6b Di2i3 Djj' Bi2j Bi3j')=> 
    /andP [] x'E d'E.
  - by case/and3P: (cmpR2 Bi3j); rewrite (eqP x'E) eq_refl.
  - case/and4P: (cmpR4b Di3i2 (cmpR_swapl Bi3j) (cmpR_swapl Bi2j)).
    by rewrite (eqP x'E) eq_refl.
  - rewrite (eqP x'E) in Bi3j'.
    case/or4P: (cmpR6b Di4i3 Djj' Bi4j Bi3j')=> /andP [] x''E d''E.
    - by case/and3P: (cmpR2 Bi3j); rewrite (eqP x''E) eq_refl.
    - by case/and4P: (cmpR4b Di4i1 Bi4j Bi1j); rewrite (eqP x''E) eq_refl.
    - by case/and3P: (cmpR2 Bi3j); rewrite (eqP x''E) eq_refl.
    by case/and4P: (cmpR4b Di4i2 Bi4j Bi2j); rewrite (eqP x''E) eq_refl.
  rewrite (eqP x'E) in Bi3j'.
  case/or4P: (cmpR6b Di4i3 Djj' Bi4j Bi3j')=> /andP [] x''E d''E.
  - by case/and3P: (cmpR2 Bi3j); rewrite (eqP x''E) eq_refl.
  - by case/and4P: (cmpR4b Di4i1 Bi4j Bi1j); rewrite (eqP x''E) eq_refl.
  - by case/and4P: (cmpR4b Di4i2 Bi4j Bi2j); rewrite (eqP x''E) eq_refl.
  by case/and4P: (cmpR4b Di4i2 Bi4j Bi2j); rewrite (eqP x''E) eq_refl.
(* This is 3.5.4.3 *)
case/or3P: (cmpR5 NZj' Bi1j); first 2 last.
- case/(cmpR0F NZi1 NZj')=> [] [x x'] /= Bi1j'.
  by case/and3P: (cmpR7 NZi1 Bi3j'); rewrite opprK (cmpR1 Bi1j').
- move/F1=> Bi1j'.
  case/or3P: (cmpR5b NZi3 Bi1j').
  - move/(cmpR3 Bi3j')=> /or3P [] xE.
    - by case/and3P: (cmpR2 Bi1j); rewrite (eqP xE) eq_refl.
    - by case/and3P: (cmpR2 Bi1j); rewrite (eqP xE) eq_refl andbF.
   rewrite -(eqP xE) in Bi3j'.
   case/or4P: (cmpR6 Di3i1 Dj'j (cmpR_rotate Bi3j') Bi1j)=> /andP [] x'E d'E.
   - by case/andP: d'E; rewrite opprK eq_refl.
   - by case/andP: d'E; rewrite (eqP x'E) opprK eq_refl.
   - by case/andP: d'E; rewrite (eqP x'E) opprK eq_refl.
   by case/andP: d'E; rewrite eq_refl.
  - move/(cmpR3 Bi3j')=> /or3P [] xE.
    - rewrite -(eqP xE) in Bi3j; move: (cmpR7 NZi3 (cmpR_swapl Bi2j)).
      by rewrite (cmpR1 Bi3j) !andbF.
    - rewrite eqr_opp in xE; case/and4P: (cmpR4b Di2i1 Bi2j Bi1j).
      by rewrite (eqP xE) eq_refl.
    rewrite -(eqP xE) in Bi3j'.
    have Djj' : j != j' by rewrite eq_sym.
    have Di2i3 : i2 != i3 by rewrite eq_sym.
    case/or4P: (cmpR6b Di2i3 Djj' (cmpR_rotate Bi2j) (cmpR_rotate Bi3j'))
          => /andP [] x'E d'E.
    - by case/and3P: (cmpR2 Bi1j); rewrite (eqP x'E) eq_refl.
    - by case/and3P: (cmpR2 Bi3j); rewrite (eqP x'E) eq_refl.
    - by case/and3P: (cmpR2 Bi1j); rewrite -(eqP x'E) eq_refl andbF.
    move: (cmpR7 NZi2 Bi1j).
    by rewrite (eqP x'E) (cmpR1 (cmpR_swapl Bi2j)) !andbF.
  move/(cmpR3 Bi3j')=> /or3P [] xE.
  - rewrite -(eqP xE) in Bi3j; case/and3P: (cmpR7 NZi4 (cmpR_rotate Bi3j)).
    by rewrite opprK (cmpR1 (cmpR_rotate Bi4j)).
  - rewrite eqr_opp in xE; case/and4P: (cmpR4b Di4i1 Bi4j Bi1j).
    by rewrite (eqP xE) eq_refl.
  rewrite -(eqP xE) in Bi3j'; have Djj' : j != j' by rewrite eq_sym.
  case/or4P: (cmpR6b Di4i3 Djj' (cmpR_rotate Bi4j) (cmpR_rotate Bi3j'))
       => /andP [] x'E d'E.
  - by case/and3P: (cmpR2 Bi1j); rewrite (eqP x'E) eq_refl.
  - by case/and3P: (cmpR2 Bi3j); rewrite (eqP x'E) eq_refl.
  - by case/and3P: (cmpR2 Bi1j); rewrite -(eqP x'E) eq_refl andbF.
  rewrite -(eqP x'E) in Bi3j.
  case/and3P: (cmpR7 NZi3 (cmpR_swapl Bi1j)).
  by rewrite (cmpR1 (cmpR_rotate Bi3j)).
case/(cmpR0F NZi1 NZj')=> [] [x x'] /= Bi1j'.
wlog: x x' x1 x2 x3 x4 x5 x6 x7 x8 i1 i2 i3 i4
      NZi1 NZi2 NZi3 NZi4 Di4i3 Di4i2 Di4i1 Di3i2 Di3i1 Di2i1  
      F1 F2 F3      
      Bi1j Bi2j Bi3j Bi4j Bi1j' Bi3j' / x == -x4 => [WL | xE].
  have Djj' : j != j' by rewrite eq_sym.
  case/or4P: (cmpR6 Di3i1 Djj' Bi3j Bi1j')=> /andP [] xE dE.
  - by apply: WL Bi1j Bi2j Bi3j Bi4j Bi1j' Bi3j' xE.
  - by apply: WL Bi1j Bi4j (cmpR_swapr Bi3j) Bi2j Bi1j' Bi3j' xE;
       rewrite // 1?eq_sym => // HH; apply: cmpR_swapr; apply: F1.
  - by apply: WL Bi1j Bi2j Bi3j Bi4j (cmpR_swapr Bi1j') Bi3j' xE;
       rewrite // 1?eq_sym => // HH; apply: cmpR_swapr; apply: F1.
  by apply: WL Bi1j Bi4j (cmpR_swapr Bi3j) Bi2j (cmpR_swapr Bi1j') Bi3j' xE;
     rewrite // 1?eq_sym => // HH; apply: cmpR_swapr; apply: F1.
rewrite {x xE}(eqP xE) in Bi1j'.
move: {Bi1j'} (cmpR_swapl Bi1j')=> Bi1j'.
move: {Bi2j} (cmpR_swapl Bi2j)=> Bi2j.
have Djj' : j != j' by rewrite eq_sym.
case/or4P: (cmpR6b Di2i1 Djj' Bi2j Bi1j')=> /andP [] x'E d'E.
- by case/and3P: (cmpR2 Bi1j); rewrite (eqP x'E) eq_refl.
- case/and4P: (cmpR4b Di3i2 (cmpR_swapl Bi3j) Bi2j).
  by rewrite (eqP x'E) eq_refl.
- rewrite (eqP x'E) in Bi1j'.
  case/and4P: (cmpR4 Dj'j (cmpR_rotate Bi1j') Bi1j).
  by rewrite eq_refl.
rewrite {x' x'E d'E}(eqP x'E) in Bi1j'.
move: {Bi1j'} (cmpR_swapl Bi1j')=> Bi1j'.
move: {Bi2j} (cmpR_swapl Bi2j)=> Bi2j.
(* This is 3.5.4.4 *)
case/or3P: (cmpR5 NZj' Bi2j).
- move/F2=> Bi2j'.
  case/or3P: (cmpR5b NZi1 Bi2j'); move/(cmpR3 Bi1j'); 
         case/or3P=> /eqP xE //.
  - by case/and3P: (cmpR2 Bi1j); rewrite xE eq_refl.
  - by case/and3P: (cmpR2 Bi2j); rewrite -xE eq_refl andbF.
  - by case/and3P: (cmpR2 Bi2j); rewrite  xE eq_refl.
  - by case/and3P: (cmpR2 Bi1j); rewrite -xE eq_refl andbF.
  - case/and4P: (cmpR4b Di3i1 Bi3j' Bi1j').
    by rewrite xE eq_refl.
  - case/and4P: (cmpR4b Di3i1 Bi3j' Bi1j').
    by rewrite xE eq_refl.
  - case/and4P: (cmpR4b Di3i2 (cmpR_swapl Bi3j') (cmpR_swapl Bi2j')).
    by rewrite -xE eq_refl.
  - case/and4P: (cmpR4 Dj'j Bi2j' Bi2j)=> _ _.
    by rewrite xE eq_refl andbF.
  case/and4P: (cmpR4 Dj'j Bi2j' Bi2j)=> _ _.
  by rewrite xE eq_refl.
- move=> x4Ii2; case/and3P: (cmpR7 NZi2 Bi1j').
  by rewrite opprK=> _ /negP [].
case/(cmpR0F NZi2 NZj')=> [[x x9] /= Bi2j'].
wlog: x x9 Bi2j' / x = x8 => [WL | xE].
  case/or3P: (cmpR5b NZi2 Bi3j').
  - move=> x2Ii2; move: {Bi1j'}(cmpR_rotate Bi1j') => Bi1j'.
    case/or3P: (cmpR3 Bi2j' x2Ii2)=> x2E.
    - by case/and3P: (cmpR2 Bi1j'); rewrite (eqP x2E) eq_refl.  
    - case/and4P: (cmpR4b Di2i1 Bi2j' Bi1j').
      by rewrite (eqP x2E) eq_refl.
    case/and4P: (cmpR4b Di2i1 Bi2j' Bi1j').
    by rewrite (eqP x2E) eq_refl.
  - move=> x3Ii2.
    case/or3P: (cmpR3 Bi2j' x3Ii2)=> x3E.
    - case/and4P: (cmpR4b Di3i1 Bi3j' Bi1j').
      by rewrite (eqP x3E) eq_refl.
    - rewrite -(eqP x3E) in Bi2j'.
      have Di1i2 : i1 != i2 by rewrite eq_sym.
      case/or4P: (cmpR6b Di1i2 Djj' (cmpR_rotate Bi1j) (cmpR_swapl Bi2j'))
           => /andP [] xE dE.
      - by case/and3P: (cmpR2 Bi2j); rewrite (eqP xE) eq_refl.
      - by case/and3P: (cmpR2 Bi1j'); rewrite (eqP xE) eq_refl.
      - case/and4P: (cmpR4 Dj'j Bi2j' (cmpR_rotate Bi2j)).
        by rewrite (eqP xE) eq_refl.
      case/and4P: (cmpR4b Di2i1 Bi2j' (cmpR_rotate Bi1j')).
      by rewrite (eqP xE) eq_refl.
    rewrite -(eqP x3E) in Bi2j'.
    have Di1i2 : i1 != i2 by rewrite eq_sym.
    case/or4P: (cmpR6b Di1i2 Djj' (cmpR_rotate Bi1j) (cmpR_rotate Bi2j'))
        => /andP [] xE dE.
    - by case/and3P: (cmpR2 Bi2j); rewrite (eqP xE) eq_refl.
    - by case/and3P: (cmpR2 Bi1j'); rewrite (eqP xE) eq_refl.
    - rewrite (eqP xE) in Bi2j'.
      by case/and4P: (cmpR4 Dj'j (cmpR_swapl Bi2j') Bi2j); rewrite  eq_refl.
    rewrite (eqP xE) in Bi2j'.
    by case/and4P: (cmpR4b Di2i1 (cmpR_swapl Bi2j') Bi1j'); rewrite eq_refl.
   move/(cmpR3 Bi2j')=> /or3P [] x3E.
   - case/and4P: (cmpR4b Di3i1 Bi3j' Bi1j').
     by rewrite (eqP x3E) eq_refl.
   - by apply: WL Bi2j' _; rewrite (eqP x3E).
   by apply: WL (cmpR_swapr Bi2j') _; rewrite (eqP x3E).
rewrite {x}xE in Bi2j'.
(* This is 3.5.4.5 *)
pose II x := inR i4 j' x .
have x1NIj4 : ~~ II x1.
  apply/negP=> /F3 Bi4j'.
  case/and3P: (cmpR7 NZi4 Bi1j').
  by rewrite(cmpR1 (cmpR_rotate Bi4j')).
have mx1NIj4 : ~~ II (- x1).
 by case/and3P: (cmpR7b NZj' Bi4j).
have [NIx2 NIx3] : ~II x2 /\ ~II (- x3).
  have NII: ~ (II x2 /\ II (- x3)).
    case; case/(cmpR0F NZi4 NZj')=> [[x x'] /= Bi4j' x3Ii4].
     wlog: x x' Bi4j' / x = - x3=> [WL|HH]; last rewrite {}HH in Bi4j'.
       case/or3P: (cmpR3 Bi4j' x3Ii4)=> xE.
       - case/and3P: (cmpR2 Bi1j).
         by rewrite -(eqP xE) eq_refl andbF.
       - by apply: WL Bi4j' _; rewrite (eqP xE).
       by apply: WL (cmpR_swapr Bi4j') _; rewrite (eqP xE).
     case/and4P: (cmpR4b Di4i3 Bi4j' Bi3j').
     by rewrite eq_refl.
  split.
    case/(cmpR0F NZi4 NZj')=> [[x x'] /= Bi4j'].
    case/or4P: (cmpR6 Di4i1 Dj'j Bi4j' (cmpR_swapl Bi1j))=> /andP [] xE dE.
    - case/and3P: (cmpR7b NZj' Bi4j); rewrite (eqP xE) opprK.
      by rewrite (cmpR1 (cmpR_swapl Bi4j')).
    - case/and3P: (cmpR7b NZj' Bi4j); rewrite (eqP xE) opprK.
      by rewrite (cmpR1 (cmpR_rotate Bi4j')).
    - case: NII; rewrite /II (cmpR1 Bi4j') (eqP xE) opprK.
      by rewrite (cmpR1 (cmpR_swapl Bi4j')).
    case: NII; rewrite /II (cmpR1 Bi4j') (eqP xE) opprK.
    by rewrite (cmpR1 (cmpR_rotate Bi4j')).
  case/(cmpR0F NZi4 NZj')=> [[x x'] /= Bi4j'].
  have Di1i4 : i1 != i4 by rewrite eq_sym.
  case/or4P: (cmpR6b Di1i4 Djj' (cmpR_rotate Bi1j) Bi4j')=> /andP [] xE dE.
  - by case/negP: x1NIj4; rewrite -(eqP xE); apply: cmpR1 (cmpR_swapl Bi4j').
  - case: NII; rewrite /II (cmpR1 Bi4j') -(eqP xE).
    by rewrite (cmpR1 (cmpR_swapl Bi4j')).
  - by case/negP: x1NIj4; rewrite -(eqP xE); apply: cmpR1 (cmpR_rotate Bi4j').
  case: NII; rewrite /II (cmpR1 Bi4j') -(eqP xE).
  by rewrite (cmpR1 (cmpR_rotate Bi4j')).
case/or3P: (cmpR5b NZi4 Bi3j')=> //.
case/(cmpR0F NZi4 NZj')=> [[x x'] /= Bi4j'].
have NIx5: ~ II x5.
  move=> x5Ii4; wlog: x x' Bi4j' / x == x5=> [WL| /eqP HH].
    case/or3P: (cmpR3 Bi4j' x5Ii4)=> xE.
    - by case/and3P: (cmpR2 (cmpR_swapl Bi2j')); rewrite (eqP xE) eq_refl.
    - by apply: WL Bi4j' _; rewrite (eqP xE).
    by apply: WL (cmpR_swapr Bi4j') _; rewrite (eqP xE).
  rewrite {}HH in Bi4j'.
  by case/and4P: (cmpR4b Di4i2 (cmpR_swapl Bi4j') Bi2j'); rewrite eq_refl.
wlog: x x' Bi4j' / x == - x4=> [WL|HH].
  case/or3P: (cmpR5b NZi4 Bi1j')=> //.
  move/(cmpR3 Bi4j')=> /or3P [] xE.
  - rewrite -(eqP xE) in Bi3j'.
    case/and4P: (cmpR4 Dj'j Bi3j' Bi3j).
    by rewrite eq_refl andbF.
  - by apply: WL Bi4j' _; rewrite (eqP xE).
  by apply: WL (cmpR_swapr Bi4j') _; rewrite (eqP xE).
rewrite {HH}(eqP HH) in Bi4j'.
have Di2i4 : i2 != i4 by rewrite eq_sym.
case/or4P: (cmpR6b Di2i4 Djj' (cmpR_swapl Bi2j) (cmpR_swapl Bi4j'))
       => /andP [] xE dE.
- by case/negP: x1NIj4; rewrite -(eqP xE) /II (cmpR1 Bi4j').
- by case: NIx5; rewrite -(eqP xE) /II (cmpR1 Bi4j').
- by case/negP: x1NIj4; rewrite -(eqP xE) /II (cmpR1 (cmpR_rotate Bi4j')).
by case: NIx5; rewrite -(eqP xE) /II (cmpR1 (cmpR_rotate Bi4j')).
Qed.

Definition ccTIirr (i : 'I_n.-1.+1) := let (x, _) := main i in x.

Local Notation gamma_ := ccTIirr.

Lemma ccTIirrE i j : i != 0 -> j != 0 -> inR i j (gamma_ j).
Proof.
move=> NZi NZj; rewrite /gamma_; case: (main j) => x.
by rewrite (negPf NZj)=> /(_ _ NZi).
Qed.

Lemma ccTIirr_inN i j j' : 
  i != 0 -> j != 0 -> j' != 0 -> j != j' -> ~~ inR i j (- gamma_ j').
Proof.
move=> NZi NZj NZj' Djj'; apply/negP=> INg.
case: (cmpR0F NZi NZj' (ccTIirrE NZi NZj'))=> [[v1 v2 /=] Hv].
by case/andP: (cmpR7b NZj Hv)=> /negP.
Qed.

Lemma ccTIirr_inP i j j' : (4 < m)%N ->
  i != 0 -> j != 0 -> j' != 0 -> j != j' -> ~~ inR i j (gamma_ j').
Proof.
move=> H4Lm NZi NZj NZj' Djj'; apply/negP=> INg.
case: (cmpR0F NZi NZj INg)=> [[v1 v2 /=] Bij].
have [i1 [NZi1 Dii1 [i2 [NZi2 Dii2 Di1i2 [i3 [NZi3 Dii3 Di1i3 Di2i3]]]]]] :
   exists i1,
    [/\ i1 != 0, i != i1 &
     exists i2, 
       [/\ i2 != 0, i != i2, i1 != i2 &
       exists i3,
         [/\ i3 !=0, i != i3, i1 != i3 & i2 != i3]]].
  have: (4 < #|'I_m.-1.+1|)%N by case: m H4Lm=> //= m1; rewrite card_ord.
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
case: (cmpR0F NZi1 NZj' (ccTIirrE NZi1 NZj'))=> [[v v3 /=] Bi1j'].
wlog: v1 v2 v v3 Bij Bi1j' / (v == -v1) && v3 '<> v2=> [WL|].
  case/or4P: (cmpR6 Dii1 Djj' Bij Bi1j'); first by apply: WL Bij Bi1j'.
  - by apply: WL (cmpR_swapr Bij) Bi1j'.
  - by apply: WL Bij (cmpR_swapr Bi1j').
  apply: WL (cmpR_swapr Bij) (cmpR_swapr Bi1j').
case/andP=> /eqP HH Dv3v2; rewrite {v}HH in Bi1j'.
case: (cmpR0F NZi2 NZj' (ccTIirrE NZi2 NZj'))=> [[v v4 /=] Bi2j'].
wlog: v1 v2 v v4 Dv3v2 Bij Bi1j' Bi2j' / (v == -v2) && v4 '<> v1=> [WL|].
  case/or4P: (cmpR6 Dii2 Djj' Bij Bi2j').
  - case/andP=> /eqP HH DD; rewrite HH in Bi2j'.
    by case/and3P: (cmpR4b Di1i2 Bi1j' Bi2j'); rewrite eq_refl.
  - by apply: WL Bij Bi1j' Bi2j'.
  - case/andP=> /eqP HH DD; rewrite HH in Bi2j'.
    by case/and3P: (cmpR4b Di1i2 Bi1j' Bi2j'); rewrite eq_refl.
  by apply: WL Bij Bi1j' (cmpR_swapr Bi2j').
case/andP=> /eqP HH Dv3v1; rewrite {v}HH in Bi2j'.
case: (cmpR0F NZi3 NZj' (ccTIirrE NZi3 NZj'))=> [[v5 v6 /=] Bi3j'].
case/or4P: (cmpR6 Dii3 Djj' Bij Bi3j'); case/andP=> /eqP HH DD; 
        rewrite HH in Bi3j'.
- by case/and3P: (cmpR4b Di1i3 Bi1j' Bi3j'); rewrite eq_refl.
- by case/and3P: (cmpR4b Di2i3 Bi2j' Bi3j'); rewrite eq_refl.
- by case/and3P: (cmpR4b Di1i3 Bi1j' Bi3j'); rewrite eq_refl.
by case/and3P: (cmpR4b Di2i3 Bi2j' Bi3j'); rewrite eq_refl.
Qed.
    
End Main.

Let ONW1 : odd #|classes W1|.
Proof.
by have:= cyclic_abelian cyclicW1; rewrite card_classes_abelian => /eqP ->.
Qed.

Let ONW2 : odd #|classes W2|.
by have:= cyclic_abelian cyclicW2; rewrite card_classes_abelian => /eqP ->.
Qed.

Let H2LNW1 : (2 < #|classes W1|)%N.
by have:= cyclic_abelian cyclicW1; rewrite card_classes_abelian => /eqP ->.
Qed.

Let H2LNW2 : (2 < #|classes W2|)%N.
by have:= cyclic_abelian cyclicW2; rewrite card_classes_abelian => /eqP ->.
Qed.

Let hcTIirr (i : Iirr W2) : 'CF(G) :=
 (ccTIirr ONW1 H2LNW1 H2LNW2 bcmp_swapl bcmp_swapr bcmp_rotate
  bcmp_exists in_bcTIirr_exists bcmp_in bcmp_diffs in_bcTIirrE
  bcmp2_diffs bcmp2_diffs_sym in_bcTIirr_cmp in_bcTIirr_cmp_sym
  bcmp_diff_opp bcmp_opp_diff bcmp_in_opp_sym bcmp_in_opp i).

Let sbcmp_swapl i j := @bcmp_swapl j i.
Let sbcmp_swapr i j := @bcmp_swapr j i.
Let sbcmp_rotate i j := @bcmp_rotate j i.
Let sbcmp_exists i j Hi Hj := @bcmp_exists j i Hj Hi.
Let sin_bcTIirr_exists i j v Hi Hj := @in_bcTIirr_exists j i v Hj Hi.
Let sbcmp_in i j := @bcmp_in j i.
Let sbcmp_diffs i j := @bcmp_diffs j i.
Let sin_bcTIirrE i j := @in_bcTIirrE j i.
Let sbcmp_diff_opp i1 j1 i2 j2 v1 v2 v3 v4 v5 Hi1i2 Hj1j2 := 
   @bcmp_diff_opp j1 i1 j2 i2 v1 v2 v3 v4 v5 Hj1j2 Hi1i2.
Let sbcmp_opp_diff i1 j1 i2 j2 v1 v2 v3 v4 v5 Hi1i2 Hj1j2 := 
   @bcmp_opp_diff j1 i1 j2 i2 v1 v2 v3 v4 v5 Hj1j2 Hi1i2.

Let vcTIirr (i : Iirr W1) : 'CF(G) :=
 (ccTIirr
   ONW2 H2LNW2 H2LNW1 sbcmp_swapl sbcmp_swapr sbcmp_rotate
   sbcmp_exists sin_bcTIirr_exists sbcmp_in sbcmp_diffs
   sin_bcTIirrE bcmp2_diffs_sym bcmp2_diffs in_bcTIirr_cmp_sym
   in_bcTIirr_cmp sbcmp_diff_opp sbcmp_opp_diff bcmp_in_opp
   bcmp_in_opp_sym i).

Let hcTIirrE: forall i j, i != 0 -> j != 0 -> in_bcTIirr i j (hcTIirr j) :=
 (ccTIirrE ONW1 H2LNW1 H2LNW2 bcmp_swapl bcmp_swapr bcmp_rotate
  bcmp_exists in_bcTIirr_exists bcmp_in bcmp_diffs in_bcTIirrE
  bcmp2_diffs bcmp2_diffs_sym in_bcTIirr_cmp in_bcTIirr_cmp_sym
  bcmp_diff_opp bcmp_opp_diff bcmp_in_opp_sym bcmp_in_opp).

Let vcTIirrE i j (Hi : i != 0) (Hj : j != 0) : in_bcTIirr i j (vcTIirr i) :=
 (ccTIirrE
   ONW2 H2LNW2 H2LNW1 sbcmp_swapl sbcmp_swapr sbcmp_rotate
   sbcmp_exists sin_bcTIirr_exists sbcmp_in sbcmp_diffs
   sin_bcTIirrE bcmp2_diffs_sym bcmp2_diffs in_bcTIirr_cmp_sym
   in_bcTIirr_cmp sbcmp_diff_opp sbcmp_opp_diff bcmp_in_opp
   bcmp_in_opp_sym Hj Hi).

Definition dcTIirr (i : Iirr W1) (j : Iirr W2) : 'CF(G) := 
  if (i == 0) then 
    if (j == 0) then '1_G else - hcTIirr j
  else
    if (j == 0) then - vcTIirr i else beta_ i j + hcTIirr j + vcTIirr i.

Local Notation x_ := dcTIirr.

End Proofs.

