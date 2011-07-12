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
Definition cyclicTIirr i j := 'chi_(dprod_idx W1xW2 (i, j)).
Local Notation w_ := cyclicTIirr.

Lemma w00 : w_ 0 0 = 1.
Proof.
rewrite /w_ dprod_idxE !chi0_1.
apply/cfun_inP=> x Wx; rewrite cfun1E Wx.
case/(mem_dprod W1xW2): Wx => y [z [W1y W2z -> _]].
by rewrite cfun_dprodE // !cfun1E W1y W2z mulr1.
Qed.

Lemma w_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof. by rewrite /w_ !dprod_idxE !chi0_1 cfun_dprod1r cfun_dprod1l. Qed.

Let linearX (i : Iirr W) : clinear ('chi_i).
Proof.
apply/char_abelianP.
by apply: cyclic_abelian; case: tiW; case.
Qed.

(* GG -- suppressed: with typed classfuns, this is subsumed by mul1r/mulr1
Lemma support_mul1l (f : {cfun gT})) : support f \subset W -> '1_W * f = f.
Proof.
move=> SsW; apply/cfunP=> g; rewrite cfunE cfuniE.
move/subsetP: SsW; move/(_ g); rewrite /fun_of_cfun /= !inE.
by case: (_ =P _)=> [->| _ -> //]; rewrite !(mulr0,mul1r).
Qed.

Lemma support_mul1r (f : {cfun gT}) : support f \subset W ->  f * '1_W = f.
Proof.
move=> SsW; apply/ffunP=> g; rewrite !ffunE.
move/subsetP: SsW; move/(_ g); rewrite /fun_of_cfun /= !inE.
by case: (_ =P _)=> [->| _ -> //]; rewrite !(mul0r,mulr1).
Qed.
*)

Definition alpha_ i j : 'CF(W) := (1 - w_ i 0) * (1 - w_ 0 j).

Lemma alphaE i j : alpha_ i j = 1 - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite /alpha_ mulr_subl mul1r mulr_subr mulr1 -w_split.
by rewrite oppr_sub !addrA addrAC (addrAC 1).
Qed.

Lemma vchar_alpha i j : alpha_ i j \in 'Z[irr W].
Proof. by rewrite vchar_mul // -chi0_1 vchar_sub ?vchar_irr. Qed.

Lemma memc_alpha i j : alpha_ i j \in 'CF(W, V).
Proof.
apply/cfun_memfP=> x; rewrite !inE negb_and negbK orbC.
have [Wx /= | /cfun0->//] := boolP (x \in W).
rewrite !cfunE cfun1E Wx /w_ !dprod_idxE !chi0_1 cfun_dprod1l cfun_dprod1r.
rewrite -{3}[x]mul1g -{4}[x]mulg1; case/orP=> [W1x | W2x]; last first.
  rewrite cfun_dprodEl // clinear_val1 ?subrr ?mul0r //.
  exact/char_abelianP/cyclic_abelian.
rewrite mulrC cfun_dprodEr // clinear_val1 ?subrr ?mul0r //.
exact/char_abelianP/cyclic_abelian.
Qed.

Definition beta_ i j : 'CF(G) := 'Ind[G] (alpha_ i j) - 1.

Lemma vchar_beta i j : beta_ i j \in 'Z[irr G].
Proof. by rewrite vchar_sub ?vchar_Ind ?vchar_alpha // -chi0_1 vchar_irr. Qed.

Lemma cfdot_w i j i' j' :
  '[w_ i j, w_ i' j'] = ((i == i') && (j == j'))%:R.
Proof. by rewrite cfdot_irr inj_eq //; exact: dprod_idx_inj. Qed.

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
by rewrite -Frobenius_reciprocity cfunRes1 // cfdot_alpha00.
Qed.

Let VsG : V \subset G^#.
Proof.
apply/subsetP=> g; rewrite !inE negb_or -andbA; case/and3P=> [GniW1 GniW2 GiW].
have WsG : W \subset G by case: tiW; case.
by rewrite (subsetP WsG) // andbT; apply: contra GniW1; move/eqP->; exact: group1.
Qed.

(* This is the first equation of  PF 3.5.1 *)
Lemma cfdot_beta_1 i j : i != 0 -> j != 0 -> '[beta_ i j, 1] = 0.
Proof.
move=> Di Dj.
by rewrite cfdot_subl cfdot_Ind_alpha_1 // -chi0_1 cfdot_irr subrr.
Qed.

(* These are the other equations of PF 3.5.1 *)
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

Lemma abelian_dim_cfun (H : {group gT}) (K : {set gT}) : 
  abelian H -> K \subset H -> \dim 'CF(H, K) = #|K|.
Proof.
move=> cHH sKH.
have idJ x: x \in H -> x ^: H = [set x].
  by move/(subsetP cHH); rewrite -sub_cent1 -astab1J astabC sub1set => /orbit1P.
rewrite (eqnP (cfun_free H K)) size_tuple.
rewrite -(card_imset (mem K) set1_inj); apply/eq_card=> xH; rewrite !inE.
apply/andP/imsetP=> [[/imsetP[x Hx ->] Kx] | [x Kx ->]] {xH}.
  by rewrite idJ ?sub1set // in Kx *; exists x.
by rewrite -{1}(idJ x) ?mem_classes ?(subsetP sKH) ?sub1set.
Qed.

Lemma dim_cyclicTIcfun : \dim 'CF(W, V) = (#|Iirr W1|.-1 * #|Iirr W2|.-1)%N.
Proof.
rewrite !card_ord abelian_dim_cfun ?(cyclic_abelian, subsetDl) // !NirrE.
have:= cyclic_abelian cyclicW1; rewrite card_classes_abelian => /eqP ->.
have:= cyclic_abelian cyclicW2; rewrite card_classes_abelian => /eqP ->.
apply: (@addnI (#|W1| + #|W2|)%N); rewrite -{1}cardsUI addnAC.
have [_ defW _ ->] := dprodP W1xW2; rewrite cards1.
have /setIidPr <-: (W1 :|: W2) \subset W by rewrite subUset -mulG_subG defW.
rewrite cardsID -(dprod_card W1xW2) -(prednK (cardG_gt0 W1)) /=.
by rewrite addn1 !addSn addnAC -mulnS mulSnr prednK.
Qed.

(* GG -- this is much too combinatorial, and as a result WAY TOO COMPLICATED
Definition base_alpha : (#|Iirr W1|.-1 * #|Iirr W2|.-1).-tuple 'CF(W) :=
  [tuple of [seq (alpha_ i j) | i <- behead (enum (Iirr W1)),
                                j <- behead (enum (Iirr W2))]].

Let diff_behead n k : k \in behead (enum 'I_n.+1) -> k != 0.
Proof.
apply: contraTneq => ->.
by rewrite -(mem_map val_inj) -behead_map val_enum_ord mem_iota.
Qed.

(* Move to seq *)
Lemma nth_allpairs (S T R : Type) (f : S -> T -> R) 
   (s : seq S) (t : seq T) ds dt dr i (n := size s) (m := size t) :
   (i < n * m)%N ->
   nth dr (allpairs f s t) i = f (nth ds s (i %/ m)%N)
                                 (nth dt t (i %% m)%N).
Proof.
rewrite {}/n /allpairs; elim: s i [::] => //= a s IH i l iLp.
rewrite nth_cat size_map -/m; case: leqP=> iLm; last first.
  by rewrite divn_small //= modn_small // (nth_map dt).
have mpos : (0 < m)%N by case: (m) iLp; rewrite ?muln0.
rewrite -{2 3}(subnK iLm) divn_addr ?dvdnn // divnn mpos addnC /=.
by rewrite modn_addr IH // -(ltn_add2l m) addnC subnK.
Qed.

Lemma free_base_alpha : free base_alpha.
Proof.
apply/freeP=> a Hs; set In := 'I__ => ij.
pose l1 := behead (enum_tuple (Iirr W1)).
have Ul1: uniq l1.
  move: (enum_uniq (Iirr W1)); rewrite /l1 /=.
  by case: (enum _)=> //= u v /andP [].
pose l2 := behead (enum_tuple (Iirr W2)).
have Ul2: uniq l2.
  move: (enum_uniq (Iirr W2)); rewrite /l2 /=.
  by case: (enum _)=> //= u v /andP [].
have sl2_pos: (0 < size l2)%N.
  rewrite size_behead -cardT card_ord /pred_Nirr.
   move: (cyclic_abelian cyclicW2); rewrite card_classes_abelian; move/eqP->.
   by case: #|_| tLW2=> [|[|]].
have GijLs (ij1 : In) : (ij1 < size l1 * size l2)%N.
  by case: ij1=> mm /=; rewrite !size_behead -!cardT.
have GijdLs (ij1 : In) : (ij1 %/ size l2 < size l1)%N.
  case: ij1=> mm /=; rewrite !size_behead -!cardT /= !card_ord /= /pred_Nirr.
  move: (cyclic_abelian cyclicW1); rewrite card_classes_abelian; move/eqP->.
  move: (cyclic_abelian cyclicW2); rewrite card_classes_abelian; move/eqP->.
  move=> HH; have Hp: (0 < #|W2|.-1)%N by case: #|_| tLW2=> [|[|]].
  by rewrite -(ltn_pmul2r Hp) (leq_ltn_trans (leq_floor _ _)).
pose i := l1`_(ij %/ size l2).
pose j := l2`_(ij %% size l2).
have<-: '[0, w_ i j]_W = 0 by rewrite -inner_prodbE linear0.
rewrite -Hs -inner_prodbE linear_sum /=.
rewrite (bigD1 ij) //= (nth_allpairs _ 0 0) -/i -/j //.
rewrite big1 ?addr0=> [|ij' Dij].
  rewrite linearZ /= inner_prodbE.
  rewrite inner_prod_alpha ?(diff_behead, mem_nth, ltn_pmod) //.
  by rewrite !eqxx [_ *: _]mulr1.
pose i' := l1`_(ij' %/ size l2).
pose j' := l2`_(ij' %% size l2).
rewrite linearZ /= inner_prodbE (nth_allpairs _ 0 0) // -/i' -/j'.
rewrite inner_prod_alpha ?(diff_behead, mem_nth, ltn_pmod) //.
case: (_ =P _); rewrite ?scaler0 //.
case: (_ =P _); rewrite ?scaler0 //.
move/eqP; rewrite nth_uniq ?ltn_mod // /eqP => Emod.
move/eqP; rewrite nth_uniq // => /eqP Ediv.
case/eqP: Dij.
move: (divn_eq ij' (size l2)).
rewrite Ediv (eqP Emod) -divn_eq /= => HH.
by apply/val_eqP=> /=; rewrite HH.
Qed.
*)

Definition alpha_base :=
  [tuple of map (prod_curry alpha_) (enum (setX [set~ ord0] [set~ ord0]))].

Lemma alpha_base_free : free alpha_base.
Proof.
apply/freeP=> s s_alpha_0 ij; case def_ij: (enum_val ij) => [i j].
have /andP[Di Dj]: (i != 0) && (j != 0).
  by rewrite -!in_setC1 -in_setX -def_ij enum_valP.
have:= congr1 (cfdotr (w_ i j)) s_alpha_0; rewrite raddf_sum raddf0 => <-.
rewrite (bigD1 ij) //= -tnth_nth tnth_map /tnth -enum_val_nth def_ij.
rewrite cfdotZl cfdot_alpha // !eqxx mulr1 big1 ?addr0 // => kl.
rewrite -tnth_nth tnth_map /tnth -enum_val_nth -(inj_eq (@enum_val_inj _ _)).
case: (enum_val kl) => k l /= => /negbTE ne_kl_ij.
by rewrite cfdotZl cfdot_alpha // -xpair_eqE -def_ij ne_kl_ij mulr0.
Qed.

(* This is PF 3.4 *)
Lemma alpha_base_is_basis : is_basis 'CF(W,V) alpha_base.
Proof.
rewrite /is_basis alpha_base_free andbT /is_span -dimv_leqif_eq.
  by rewrite (eqnP alpha_base_free) size_tuple cardsX !cardsC1 dim_cyclicTIcfun.
by rewrite -span_subsetl; apply/allP=> _ /imageP[[i j] _ ->]; exact: memc_alpha.
Qed.

End Proofs.
