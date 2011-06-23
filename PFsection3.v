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
apply/cfunP=> g; case: (boolP (g \in X))=> [GiX|GniX]; last first.
  by rewrite 2!cfunE (negPf GniX) mul0r (cfunS0 Ctheta).
rewrite 2!cfunE GiX mul1r.
rewrite !cfunE (bigID (fun g => g \in 'N_G(X))) /=.
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
  by rewrite (cfunS0 Cphi) ?(cfunE,conjC0,mulr0,GniX,GiNG,inE).
rewrite 3!cfunE GiNG mul1r.
move/cfunP: ti_restrict_induced; move/(_ g).
rewrite 2!cfunE GiX mul1r => ->.
by rewrite !cfunE subrr mul0r.
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
by apply/cfunP=> x; rewrite mxE !(cfuniE, cfunE) -natr_mul mulnb andbb.
Qed.

End MoreDefinitions.

