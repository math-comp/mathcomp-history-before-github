(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1.

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

(* This is Isaacs' 7.7 *)
Section TiInducedIso.

Variables (gT : finGroupType) (G : {group gT}) (X: {set gT}).
Variables (phi theta : {cfun gT}).

Hypothesis TiX :  trivIset (X^# :^: G).
Hypothesis Cphi : phi \in 'CF('N_G(X), X).
Hypothesis Ctheta : theta \in 'CF('N_G(X), X).
Hypothesis theta1 : theta 1%g = 0.

Lemma ti_restrict_induced : 'Res[X] ('Ind[G, 'N_G(X)] theta) = theta.
Proof.
apply/ffunP=> g; case: (boolP (g \in X))=> [GiX|GniX]; last first.
  by rewrite 2!cfunE (negPf GniX) mul0r -(cfunS0 Ctheta GniX).
rewrite 2!ffunE GiX mul1r.
rewrite !ffunE (bigID (fun g => g \in 'N_G(X))) /=.
rewrite (eq_bigr (fun i : gT => theta g))=> [/= | h]; last first.
  by case/andP=> HiG HiN; rewrite (cfunJ _ Ctheta).
rewrite sumr_const big1 ?addr0=> [| h].
  set u := #|_|; suff->: u = #|'N_G(X)|.
    by rewrite mulrC -[theta g *+ _]mulr_natr mulfK // neq0GC.
  apply: eq_card=> i; rewrite [X in X = _]/= {1}/in_mem /=.
  by case: (boolP (i \in _))=> //; rewrite inE; move/negPf->.
case/andP=> HiG HiN.
case: (boolP (g^h == 1%g))=> [/eqP-> //| Dgh].
rewrite (cfunS0 Ctheta) //.
apply/negP=> GHniX.
suff: [disjoint X^# & (X :^ h)^#].
  move/pred0P; move/(_ (g^h)%g)=> /=; rewrite !inE Dgh GHniX /=.
  by move/idP; case; apply/imsetP; exists g.
rewrite -conjD1g (trivIsetP TiX) //.
- by apply/imsetP; exists 1%g; [exact: group1| rewrite conjsg1].
- by apply/imsetP; exists h.
rewrite conjD1g;  apply/eqP=> HH1; case/negP: HiN.
rewrite !inE HiG /=.
apply/subsetP=> k.
case/imsetP=> k1 K1iX ->.
case: (boolP (k1 == 1%g)) K1iX=> [/eqP-> | HH2 HH3].
  by rewrite conj1g.
have[/subsetP]: X^# \subset X by apply/subsetP=> x; rewrite !inE; case/andP.
apply; rewrite HH1 !inE; apply/andP; split; last first.
  by apply/imsetP; exists k1.
apply/eqP=> HH4; case/eqP: HH2.
by rewrite -(conj1g (h^-1)) -HH4 -conjgM mulgV conjg1.
Qed.

Lemma ti_induced_iso : 
 '['Ind[G, 'N_G(X)] theta, 'Ind[G, 'N_G(X)] phi]_G = '[theta, phi]_'N_G(X).
Proof.
have NsG: 'N_G(X) \subset G.
  by apply/subsetP=> h; rewrite inE => /andP [].
rewrite inner_conj -frobenius_reciprocity -?inner_conj //; last first.
- by apply: memc_induced=> //; apply: memcW Ctheta.
- by apply: memcW Cphi.
apply/eqP; rewrite -subr_eq0 /=; apply/eqP.
 (* why this does not work rewrite -!inner_prodbE -linear_sub ? *)
rewrite -!inner_prodbE;  set u := inner_prodb _ _.
have Fu : linear (u : _ -> algC^o) by apply: inner_prodb_is_linear.
move: (linear_sub (Linear Fu))=> /= <-; rewrite /u inner_prodbE.
rewrite inner_prodE big1 ?mulr0 // => g GiNG.
case: (boolP (g \in X))=> [GiX | GniX]; last first.
  by rewrite (cfunS0 Cphi) ?(ffunE,conjC0,mulr0,GniX,GiNG,inE).
rewrite 3!cfunE GiNG mul1r.
move/ffunP: ti_restrict_induced; move/(_ g).
rewrite 2!ffunE GiX mul1r => ->.
by rewrite !ffunE subrr mul0r.
Qed.

End TiInducedIso.

Section Definitions.

Variables (gT : finGroupType) (G W W1 W2 Wi : {set gT}).

Definition cyclicTIhypothesis :=
  [/\ [/\ W1 \x W2 = W, cyclic W, odd #|W| & W \subset G],
      [/\ W1 != 1, W2 != 1 & coprime #|W1| #|W2| ]
    & trivIset ((W :\: (W1 :|: W2)) :^: G)]%g.


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

Definition alpha_ (i : Iirr W1) (j : Iirr W2) := 
 ('1_W - w_ i 0) * ('1_W - w_ 0 j).

Lemma alphaE i j : alpha_ i j = '1_W - w_ i 0 - w_ 0 j + w_ i j.
Proof.
rewrite /alpha_ mulr_subr !mulr_subl cfuniM setIid -w_split oppr_add opprK. 
by rewrite !addrA !(support_mul1l, support_mul1r) //;
   (apply/subsetP=> g; rewrite !inE; apply: contraR=> HH; apply/eqP;
   apply: cfun0 (memc_irr _) HH).
Qed.

Lemma memc_alpha i j : alpha_ i j \in 'CF(W, V).
Proof.
rewrite memcE; apply/andP; split; last first.
  by apply: memc_prod; rewrite memv_subr !(memc_irr, memc1).
apply/subsetP=> g; rewrite !inE !cfunE; apply: contraR.
have F1 : W1 :&: W2 = 1%g by move/ dprodP: W1xW2; case.
rewrite negb_and negbK -orbA; case/or3P=> HH; last first.
- rewrite (negPf HH).
  move: (cfun0 (memc_irr ((dprod_idx W1xW2 i 0))) HH); rewrite /fun_of_cfun /= => ->.
  move: (cfun0 (memc_irr ((dprod_idx W1xW2 0 j))) HH); rewrite /fun_of_cfun /= => ->.
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

Lemma dim_cfun : \dim 'CF(W, V) = ((Nirr W1).-1 * (Nirr W2).-1)%N.
Proof.
rewrite abelian_dim_cfun ?(cyclic_abelian, subsetDl) //; last first.
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

End Proofs.
