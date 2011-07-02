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

Definition cycTIirr_row :=
  ('1_W : {cfun gT})
    :: filter [pred xi | (Wi \subset cker W xi) && (xi != '1_W)]
              (irr G).

Definition cyclicTIset of cyclicTIhypothesis := W :\: (W1 :|: W2).

End Definitions.

Section MoreDefinitions.

Variables (gT : finGroupType) (G W W1 W2 : {group gT}).

Hypothesis tiW : cyclicTIhypothesis G W W1 W2.

Let w1 := #|W1|.
Let w2 := #|W2|.
Let V := cyclicTIset tiW.

Definition cycTIirr_mx of cyclicTIhypothesis G W W1 W2 :=
  \matrix_(i < (Zp_trunc w1).+2, j < (Zp_trunc w2).+2)
     ((cycTIirr_row G W W2)`_i * (cycTIirr_row G W W1)`_j).

Local Notation ww := (cycTIirr_mx tiW).

Lemma cycTIirr00 : ww 0 0 = '1_W.
Proof.
by apply/ffunP=> x; rewrite mxE !(cfuniE, ffunE) -natr_mul mulnb andbb.
Qed.

End MoreDefinitions.

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

Definition w_ (i : Iirr W1) (j : Iirr W2) := 'xi_(dprod_idx W1xW2 i j).

Lemma w00 : w_ 0 0 = '1_W.
Proof.
rewrite /w_ dprod_idxE -!cfuni_xi0 cfun_dprod1r.
apply/ffunP=> i; rewrite !cfunE.
case: (boolP (_ \in _)); last by rewrite !mul0r.
by rewrite (mem_dprod W1xW2); case/andP=>->; rewrite mul1r.
Qed.

Lemma w_split i j : w_ i j = w_ i 0 * w_ 0 j.
Proof.
by rewrite /w_ !dprod_idxE -!cfuni_xi0 cfun_dprod1r cfun_dprod1l.
Qed.

Let linearX (i : Iirr W) : clinear W ('xi_ i).
Proof.
apply/char_abelianP.
by apply: cyclic_abelian; case: tiW; case.
Qed.

Lemma support_mul1l (f : {cfun gT}) : support f \subset W -> '1_W * f = f.
Proof.
move=> SsW; apply/cfunP=> g; rewrite !cfunE.
move/subsetP: SsW; move/(_ g); rewrite /fun_of_cfun /= !inE.
by case: (_ =P _)=> [->| _ -> //]; rewrite !(mulr0,mul1r).
Qed.

Lemma support_mul1r (f : {cfun gT}) : support f \subset W ->  f * '1_W = f.
Proof.
move=> SsW; apply/ffunP=> g; rewrite !ffunE.
move/subsetP: SsW; move/(_ g); rewrite /fun_of_cfun /= !inE.
by case: (_ =P _)=> [->| _ -> //]; rewrite !(mul0r,mulr1).
Qed.

Definition alpha_ (i : Iirr W1) (j : Iirr W2) : {cfun gT} := 
 ('1_W - w_ i 0) * ('1_W - w_ 0 j).

Lemma alphaE i j : alpha_ i j = '1_W - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite /alpha_ mulr_subr !mulr_subl cfuniM setIid -w_split oppr_add opprK. 
by rewrite !addrA !(support_mul1l, support_mul1r) //;
   (apply/subsetP=> g; rewrite !inE; apply: contraR=> HH; apply/eqP;
   apply: cfun0 (memc_irr _) HH).
Qed.

Lemma vchar_alpha i j : alpha_ i j \in 'Z[irr W].
Proof.
rewrite alphaE; apply: vchar_add; last by apply: vchar_irr.
do 2 (apply: vchar_sub; last by apply: vchar_irr).
rewrite cfuni_xi0; apply: vchar_irr.
Qed.

Lemma memc_alpha i j : alpha_ i j \in 'CF(W, V).
Proof.
rewrite memcE; apply/andP; split; last first.
  by apply: memc_prod; rewrite memv_subr !(memc_irr, memc1).
apply/subsetP=> g; rewrite !inE !cfunE; apply: contraR.
have F1 : W1 :&: W2 = 1%g by move/ dprodP: W1xW2; case.
pose d i j := dprod_idx W1xW2 i j.
rewrite negb_and negbK -orbA; case/or3P=> HH; last first.
- rewrite (negPf HH).
  move: (cfun0 (memc_irr (d i 0)) HH); rewrite /fun_of_cfun /= => ->.
  move: (cfun0 (memc_irr (d 0 j)) HH); rewrite /fun_of_cfun /= => ->.
  by rewrite !subr0 mul0r.
- rewrite /w_ !dprod_idxE -!cfuni_xi0 cfun_dprod1r cfun_dprod1l !ffunE.
  rewrite -{3}[g]mul1g divgrMid //.
  have: clinear W1 ('xi_i) by apply/char_abelianP; apply: cyclic_abelian.
  by move/clinear_val1=> ->; rewrite mulr1 subrr mul0r.
rewrite /w_ !dprod_idxE -!cfuni_xi0 cfun_dprod1r cfun_dprod1l !ffunE.
rewrite -{6}[g]mulg1 remgrMid //.
have: clinear W2 ('xi_j) by apply/char_abelianP; apply: cyclic_abelian.
by move/clinear_val1=> ->; rewrite mulr1 subrr mulr0.
Qed.

Definition beta_ (i : Iirr W1) (j : Iirr W2) : {cfun gT} := 
  'Ind[G, W] (alpha_ i j) - '1_G.

Lemma vchar_beta i j : beta_ i j \in 'Z[irr G].
Proof.
rewrite /beta_; apply: vchar_sub.
  by apply: vchar_induced (vchar_alpha _ _); case: tiW; case.
by rewrite cfuni_xi0; apply: vchar_irr.
Qed.

Definition inner_prod_w i j i' j' :
  '[w_ i j, w_ i' j']_W = ((i == i') && (j == j'))%:R.
Proof.
apply/eqP; rewrite irr_orthonormal -eqN_eqC; apply/eqP.
case: (boolP (dprod_idx _ _ _ == _)).
  by move/eqP; move/dprod_idx_inj->.
by case: (boolP (_ && _))=> //; case/andP=> /eqP-> /eqP->; case/negP.
Qed.

Lemma inner_prod_alpha i j i' j' : i' != 0 -> j' != 0 ->
  '[alpha_ i j, w_ i' j']_W = ((i == i') && (j == j'))%:R.
Proof.
move=> Di' Dj'.
rewrite -inner_prodbE alphaE !linearD !linearN -w00 /= !inner_prodbE.
rewrite !inner_prod_w.
rewrite [0 == i']eq_sym (negPf Di') [0 == j']eq_sym (negPf Dj') !andbF !subr0.
by rewrite add0r.
Qed.

Lemma inner_prod_alpha00 i j : i != 0 -> j != 0 ->
  '[alpha_ i j, '1_W]_W = 1.
Proof.
move=> Di Dj.
rewrite -inner_prodbE alphaE !linearD !linearN -w00 /= !inner_prodbE.
rewrite !inner_prod_w !eqxx /=.
by rewrite (negPf Di) (negPf Dj) !andbF !subr0 addr0.
Qed.

Lemma norm_alpha i j :  i != 0 -> j != 0 ->'[alpha_ i j]_W = 4%:R.
Proof.
move=> Di Dj.
rewrite alphaE !(raddf_sub,raddfD) /=.
rewrite -!inner_prodbE !(linear_sub, linearD) -w00 /= !inner_prodbE.
rewrite !inner_prod_w !eqxx ![0 == _]eq_sym (negPf Di) (negPf Dj).
by rewrite !(subr0, sub0r, add0r, addr0) opprK -!natr_add.
Qed.

Lemma inner_prod_ind_alpha_1 i j : i != 0 -> j != 0 -> 
  '['Ind[G, W] (alpha_ i j), '1_G]_G = 1.
Proof.
move=> Di Dj; have WsG : W \subset G by case: tiW; case.
rewrite -frobenius_reciprocity //; last by apply: memc_is_char (is_char1 _).
  by rewrite crestrict1; move/setIidPl: WsG->; rewrite inner_prod_alpha00.
by apply: memc_Zirr (vchar_alpha _ _).
Qed.

Let VsG : V \subset G^#.
Proof.
apply/subsetP=> g; rewrite !inE negb_or -andbA; case/and3P=> [GniW1 GniW2 GiW].
have WsG : W \subset G by case: tiW; case.
by rewrite (subsetP WsG) // andbT; apply: contra GniW1; move/eqP->; exact: group1.
Qed.

(* This is the first equation of  PF 3.5.1 *)
Lemma inner_prod_beta_1 i j : i != 0 -> j != 0 -> '[beta_ i j, '1_G]_G = 0.
Proof.
move=> Di Dj.
rewrite /beta_ -inner_prodbE linear_sub /= !inner_prodbE.
by rewrite inner_prod_ind_alpha_1 // cfuni_xi0 irr_orthonormal eqxx subrr.
Qed.

(* These are the other equations of PF 3.5.1 *)
Lemma inner_prod_beta i j i' j' : i != 0 -> j != 0 -> i' != 0 -> j' != 0 -> 
  '[beta_ i j, beta_ i' j']_G =
    if (i == i') && (j == j') then 3%:R else ((i == i') + (j == j'))%:R.
Proof.
move=> Di Dj Di' Dj'. 
rewrite /beta_ raddf_sub /= inner_prod_beta_1 // subr0.
rewrite -inner_prodbE linear_sub /= !inner_prodbE.
have nTi: normedTI (W :\: (W1 :|: W2)) G W by case: tiW.
rewrite (Frobenius_isometry _ nTi) ?memc_alpha //.
rewrite ['['1__,_]__]inner_conj inner_prod_ind_alpha_1 // conjC1.
rewrite !alphaE !(raddf_sub,raddfD) /=.
rewrite -!inner_prodbE !(linear_sub, linearD) -w00 /= !inner_prodbE.
rewrite !inner_prod_w !eqxx ![0 == _]eq_sym.
rewrite (negPf Di) (negPf Dj) (negPf Di') (negPf Dj').
by do 2 case: (_ == _); 
   rewrite !(subr0, sub0r, add0r, addr0, opprK,
             (I,natr_add), (I, (@natr_sub _ _ 1))).
Qed.

Lemma abelian_dim_cfun (H : {group gT}) (K : {set gT}) : 
  abelian H -> K \subset H -> \dim 'CF(H, K) = #|K|.
Proof.
move=> AH KsH.
rewrite (eqnP (cfun_free H K)) size_tuple.
have->: #|K| = size [seq ([ffun j => (i == j)%:R] : {cfun gT}) | i <- enum K].
  by rewrite size_map cardE.
apply: perm_eq_size; apply: uniq_perm_eq.
- apply: filter_uniq.
  rewrite map_inj_in_uniq ?enum_uniq //= => u v Hu Hv HH.
  apply/setP=> g.
  move/ffunP: HH; move/(_ g); rewrite !ffunE.
  by move/eqP; rewrite -eqN_eqC; move/eqP; do 2 case: (_ \in _).
- rewrite map_inj_in_uniq ?enum_uniq // => u v _ _.
  move/ffunP; move/(_ v); rewrite !ffunE eqxx.
  by case: (_ =P _)=> //= _; move/eqP; rewrite eq_sym oner_eq0.
have F0: forall h, h \in H -> h ^: H = set1 h.
  move=> h HiH; apply/setP=> k; rewrite !inE.
  apply/imsetP/eqP=> [[l LiH ->]|<-]; last by exists 1%g; rewrite !(group1,conjg1).
  rewrite conjgE; move/centP: (subsetP AH _ HiH); move/(_ _ LiH)=> ->.
  by rewrite mulgA mulVg mul1g.
move=> f; rewrite mem_filter; apply/andP/mapP=> [|[g]].
  case=> SsK; case/mapP=> u; rewrite mem_enum.
  case/imsetP=> h HiH -> Hf; move: SsK; rewrite Hf /= => SsK.
  exists h; last first.
    by apply/ffunP=> g; rewrite F0 // !ffunE inE eq_sym.
  rewrite mem_enum; apply: (subsetP SsK).
  by rewrite !inE F0 // cfunE inE eqxx nonzero1r.
rewrite mem_enum => Hg ->; split.
  apply/subsetP=> h; rewrite !inE cfunE.
  by case: (g =P h)=> [<- _ | _]; last by case/eqP.
apply/mapP; exists (g ^: H).
  by rewrite mem_enum mem_classes // (subsetP KsH _ Hg).
apply/ffunP=> h; rewrite !ffunE.
by rewrite F0 ?(subsetP KsH) // inE eq_sym.
Qed.

Lemma dim_cfun : \dim 'CF(W, V) = (#|Iirr W1|.-1 * #|Iirr W2|.-1)%N.
Proof.
rewrite !card_ord abelian_dim_cfun ?(cyclic_abelian, subsetDl) //; last first.
apply: (@addnI #|W1 :|: W2|).
have /setIidPr {1}<-: (W1 :|: W2) \subset W.
  case/dprodP: W1xW2=> _ <- _ _. 
  by rewrite subUset !(mulg_subl, mulg_subr, group1).
rewrite cardsID -(dprod_card W1xW2) !NirrE.
move: (cyclic_abelian cyclicW1); rewrite card_classes_abelian; move/eqP->.
move: (cyclic_abelian cyclicW2); rewrite card_classes_abelian; move/eqP->.
apply: (@addnI #|W1 :&: W2|); rewrite addnA [X in _ = (X + _)%N]addnC cardsUI.
move/ dprodP: W1xW2; case=> _ _ _ ->.
rewrite  cards1.
case: #|_| (cardG_gt0 W1) (cardG_gt0 W2) => // m; case: #|_| => //= n _ _.
by rewrite mulnS mulSn add1n -addnS -[(n + _).+1]addSn addnA.
Qed.

Definition base_alpha : _.-tuple {cfun gT} :=
  [tuple of [seq (alpha_ i j) | i <- behead (enum (Iirr W1)),
                                j <- behead (enum (Iirr W2))]].

End Proofs.
