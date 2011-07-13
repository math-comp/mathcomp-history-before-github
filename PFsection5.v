(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 5: coherence                          *)
(* Defined here:                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Four.

(* This is Peterfalvi (4.1). *)

Variable gT : finGroupType.

Lemma vchar_pairs_orthonormal (X : {group gT}) (a b c d : 'CF(X)) u v :
    {subset (a :: b) <= 'Z[irr X]} /\ {subset (c :: d) <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& isRealC u, isRealC v, u != 0 & v != 0] ->
    [&& '[a - b, u *: c - v *: d] == 0,
         (a - b) 1%g == 0 & (u *: c - v *: d) 1%g == 0] ->
    orthonormal [:: a; b; c; d].
Proof.
have osym2 (e f : 'CF(X)) : orthonormal (e :: f) -> orthonormal (f :: e).
  by rewrite !(orthonormal_cat [::_] [::_]) orthogonal_sym andbCA.
have def_o f S: orthonormal (f :: S) -> '[f : 'CF(X)] = 1.
  by case/andP=> /andP[/eqP].
case=> /allP/and3P[Za Zb _] /allP/and3P[Zc Zd _] /andP[o_ab o_cd].
rewrite (orthonormal_cat (a :: b)) o_ab o_cd /=.
case/and4P=> /eqP r_u /eqP r_v nz_u nz_v /and3P[o_abcd ab1 cd1].
wlog suff: a b c d u v Za Zb Zc Zd o_ab o_cd r_u r_v nz_u nz_v o_abcd ab1 cd1 /
  '[a, c]_X == 0.
- move=> IH; rewrite /orthogonal /= !andbT (IH a b c d u v) //=.
  have vc_sym (e f : 'CF(X)) : ((e - f) 1%g == 0) = ((f - e) 1%g == 0).
    by rewrite -oppr_sub cfunE oppr_eq0.
  have ab_sym e: ('[b - a, e] == 0) = ('[a - b, e] == 0).
    by rewrite -oppr_sub cfdotNl oppr_eq0.
  rewrite (IH b a c d u v) // 1?osym2 1?vc_sym ?ab_sym //=.
  rewrite -oppr_eq0 -cfdotNr oppr_sub in o_abcd.
  by rewrite (IH a b d c v u) ?(IH b a d c v u) // 1?osym2 1?vc_sym ?ab_sym.
apply: contraLR cd1 => nz_ac.
have /and4P[/and3P[/eqP a1 /eqP b1 _] _ /andP[/andP[/eqP ab0 _] _] _] := o_ab.
have /and4P[/and3P[/eqP c1 /eqP d1 _] _ /andP[/andP[/eqP cd0 _] _] _] := o_cd.
have [ea [ia def_a]] := vchar_norm1P Za a1.
have{nz_ac} [e defc]: exists e : bool, c = (-1) ^+ e *: a.
  have [ec [ic def_c]] := vchar_norm1P Zc c1; exists (ec (+) ea).
  move: nz_ac; rewrite def_a def_c scalerA; rewrite -signr_addb addbK.
  rewrite cfdotZl cfdotZr cfdot_irr mulrA mulrC mulf_eq0.
  by have [-> // | _]:= ia =P ic; rewrite eqxx.
have def_vbd: v * '[b, d]_X = - ((-1) ^+ e * u).
  apply/eqP; have:= o_abcd; rewrite cfdotDl cfdotNl !raddf_sub /=.
  rewrite defc !cfdotZr a1 (cfdotC b) ab0 rmorph0 mulr1.
  rewrite -[a]scale1r -{2}[1]/((-1) ^+ false) -(addbb e) signr_addb -scalerA.
  rewrite -defc cfdotZl cd0 !mulr0 opprK addrA !subr0 mulrC addrC addr_eq0.
  by rewrite rmorph_sign r_u r_v.
have nz_bd: '[b, d] != 0.
  move/esym/eqP: def_vbd; apply: contraTneq => ->.
  by rewrite mulr0 oppr_eq0 mulf_eq0 signr_eq0.
have{nz_bd} defd: d = '[b, d] *: b.
  move: nz_bd; have [eb [ib ->]] := vchar_norm1P Zb b1.
  have [ed [id ->]] := vchar_norm1P Zd d1.
  rewrite scalerA cfdotZl cfdotZr rmorph_sign mulrA cfdot_irr.
  have [-> _ | _] := ib =P id; last by rewrite !mulr0 eqxx.
  by rewrite mulr1 mulrAC -!signr_addb addbb.
rewrite defd scalerA def_vbd scaleNr opprK defc scalerA mulrC -raddfD cfunE.
rewrite !mulf_neq0 ?signr_eq0 // -(subrK a b) -oppr_sub addrCA 2!cfunE.
rewrite (eqP ab1) oppr0 add0r cfunE -mulr2n -mulr_natl mulf_eq0 -(eqN_eqC _ 0).
by rewrite /= def_a cfunE mulf_eq0 signr_eq0 /= irr1_neq0.
Qed.

End Four.

Section Five.

Variable gT : finGroupType.

(* This is Peterfalvi, Definition (5.1). *)
(* It is unclear whether the non-triviality condiiton is used at all. *)
(* We strengthen the Z-linearity condition on tau1 to C-linearity, because in *)
(* all applications tau1 is constructed from a basis of 'Z[S, A].             *)
Definition coherent (L G : {set gT}) S A tau :=
  [/\ exists2 theta, theta \in 'Z[S, A] & theta != 0
    & exists2 tau1 : {linear 'CF(L) -> 'CF(G)},
        {in 'Z[S], isometry tau1, to 'Z[irr G]}
      & {in 'Z[S, A], tau1 =1 tau}].

(* This is Peterfalvi, Hypothesis (5.2). *)
(* The Z-linearity constraint on tau will be expressed by an additive or      *)
(* linear structure on tau. Also, we allow S to contain virtual character.    *)
Definition precoherent L G S tau R :=
  [/\ (*a*) {subset S <= 'Z[irr L]} /\ conjC_closed S,
      (*b*) {in 'Z[S, L^#], isometry tau, to 'Z[@irr gT G, G^#]},
      (*c*) pairwise_orthogonal S,
      (*d*) {in S, forall xi : 'CF(L : {set gT}),
              [/\ {subset R xi <= 'Z[irr G]}, orthonormal (R xi)
                & tau (xi - xi^*)%CF = \sum_(alpha <- R xi) alpha]}
    & (*e*) {in S &, forall xi phi : 'CF(L),
              orthogonal phi (xi :: xi^*%CF) -> orthogonal (R phi) (R xi)}].

(* This is Peterfalvi (5.2)(a). *)
Lemma irr_precoherent (L G : {group gT}) S tau :
    [/\ uniq S, {subset S <= irr L} & conjC_closed S] ->
    {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]} ->
  {R | precoherent S tau R}.
Proof.
move=> [U_S irrS clC_S] [isoL Ztau].
have vcS: {subset S <= 'Z[irr L]}.
  move=> _ /irrS/irrP[i ->]; exact: irr_vchar.
have orthS: pairwise_orthogonal S.
  apply/orthonormal_orthogonal/orthonormalP.
  split=> //= _ _ /irrS/irrP[i ->] /irrS/irrP[j ->].
  by rewrite (inj_eq (@chi_inj _ L)) cfdot_irr.
have freeS := orthogonal_free orthS.
pose beta chi := tau (chi - chi^*)%CF; pose eqBP := _ =P beta _.
have Zbeta: {in S, forall chi, chi - (chi^*)%CF \in 'Z[S, L^#]}.
  move=> chi Schi.
  have [/irrP[i def_chi] /andP[_ /= Schi']] := (irrS _ Schi, clC_S _ Schi).
  rewrite vchar_split cfunD1E sub_vchar ?mem_vchar ?subT //= def_chi.
  by rewrite !cfunE isNatC_conj ?isNatC_irr1 ?subrr.
pose sum_beta chi R := \sum_(alpha <- R) alpha == beta chi. 
pose Zortho R := all (mem 'Z[irr G]) R && orthonormal R.
have R chi: {R : 2.-tuple 'CF(G) | (chi \in S) ==> sum_beta chi R && Zortho R}.
  apply: sigW; case Schi: (chi \in S) => /=; last by exists [tuple 0; 0].
  move/(_ _ Schi) in Zbeta; have /irrP[i def_chi] := irrS _ Schi.
  have: '[beta chi] = 2%:R.
    have /andP[/= /negbTE odd_chi Schi'] := clC_S _ Schi.
    rewrite isoL // cfnormD cfnormN cfdotNr def_chi -conjC_IirrE !cfdot_irr.
    rewrite !eqxx -(inj_eq (@chi_inj _ L)) conjC_IirrE -def_chi eq_sym odd_chi.
    by rewrite oppr0 rmorph0 !addr0 -natr_add.
  case/vchar_small_norm; rewrite ?(vcharW (Ztau _ _)) // => R [oR ZR sumR].
  by exists R; apply/and3P; split; [exact/eqP | exact/allP | ].
exists (fun xi => val (val (R xi))); split=> // [chi Schi | chi phi Schi Sphi].
  by case: (R chi) => Rc /=; rewrite Schi => /and3P[/eqBP-> /allP].
case/andP => /and3P[/= /eqP opx /eqP opx' _] _.
have{opx opx'} obpx: '[beta phi, beta chi] = 0.
  rewrite isoL ?Zbeta // cfdot_subl !cfdot_subr -{3}[chi]cfConjCK.
  by rewrite -!conj_cfdot opx opx' rmorph0 !subr0.
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

(*
Section PreCoherentProperties.

Variable R : {cfun gT} -> seq {cfun gT}.
Variables (m : nat) (L G : {group gT}) (S : m.-tuple {cfun gT}).
Variable tau : {additive {cfun gT} -> {cfun gT}}.
Hypothesis isoL : {in 'Z[S, L^#] &, isometry L G tau}.
Hypothesis cohR : precoherent R isoL.

Lemma precoherent_split xi beta :
    xi \in S -> beta \in 'Z[irr G] ->
    exists X : {cfun gT}, exists Y : {cfun gT},
  [/\ beta = X - Y, X \in 'Z[R xi] & orthogonal G [:: Y] (R xi)].
Proof.
move=> Sxi VCbeta.

(* This is Peterfalvi (5.4) *)
Lemma precoherent_norm xi psi (tau1 : {additive {cfun gT} -> {cfun gT}}) X Y :
    [/\ xi \in S, psi \in 'Z[irr G] & orthogonal L [:: xi; xi^*%CF] [:: psi]] ->
    let S0 := [:: xi - psi; xi - xi^*%CF] in
    {in 'Z[S0] &, isometry L G tau1}
      /\ {in 'Z[S0], forall phi, tau1 phi \in 'Z[irr G]} ->
    tau1 (xi - xi^*%CF) = tau (xi - xi^*%CF) ->
    [/\ tau1 (xi - psi) = X - Y, X \in 'Z[R xi]
      & orthogonal G [:: Y] (R xi)] ->
 [/\ (*a*) '[xi]_L <= '[X]_G
   & (*b*) '[psi]_L <= '[Y]_G ->
           [/\ '[X]_G = '[xi]_L, '[Y]_G = '[psi]_L
             & exists2 E, subseq E (R xi) & X = \sum_(alpha <- E) alpha]].
Proof.

                           of {in 'Z[S, A], isometry L G tau} :

End PreCoherentProperties.
*)

End Five.