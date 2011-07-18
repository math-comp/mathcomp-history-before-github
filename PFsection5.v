(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius.
Require Import matrix mxalgebra mxrepresentation vector.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 (* PFsection2 PFsection3 *) PFsection4.

(******************************************************************************)
(* This file covers Peterfalvi, Section 5: Coherence.                         *)
(* Defined here:                                                              *)
(*    coherent S A tau <-> (S, A, tau) is coherent, i.e., there is a linear   *)
(*                         isometry from 'Z[S] to 'Z[irr G] that coincides    *)
(*                         with tau on 'Z[S, A] != 0 (where S : seq 'CF(L)).  *)
(* subcoherent S tau R <-> S : seq 'cfun(L) is non empty, pairwise orthogonal *)
(*                         and closed under complex conjugation, tau is an    *)
(*                         isometry from 'Z[S, L^#] to virtual characters in  *)
(*                         G that maps the difference chi - chi^*, for each   *)
(*                         chi \in S, sum of an orthonormal family R chi of   *)
(*                         virtual characters of G; in addition R chi and     *)
(*                         R phi are orth0gonal unless phi \in chi :: chi^*.  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Five.

Variable gT : finGroupType.

(* This is Peterfalvi, Definition (5.1). *)
(* The inclusion of the non-triviality condition is dubious: its status is    *)
(* dubious in the negated form of the predicate ("not coherent" apparently    *)
(* excludes "empty", e.g., in Peterfalvi (6.2)).                              *)
Definition coherent (L G : {set gT}) S A tau :=
  [/\ exists2 theta, theta \in 'Z[S, A] & theta != 0
    & exists2 tau1 : {linear 'CF(L) -> 'CF(G)},
        {in 'Z[S], isometry tau1, to 'Z[irr G]}
      & {in 'Z[S, A], tau1 =1 tau}].

Prenex Implicits is_char.
(* This is Peterfalvi, Hypothesis (5.2). *)
(* The Z-linearity constraint on tau will be expressed by an additive or      *)
(* linear structure on tau.                                                   *)
Definition subcoherent L G S tau R :=
  [/\ (*a*) all is_char S /\ conjC_closed S,
      (*b*) {in 'Z[S, L^#], isometry tau, to 'Z[@irr gT G, G^#]},
      (*c*) pairwise_orthogonal S,
      (*d*) {in S, forall xi : 'CF(L : {set gT}),
              [/\ {subset R xi <= 'Z[irr G]}, orthonormal (R xi)
                & tau (xi - xi^*)%CF = \sum_(alpha <- R xi) alpha]}
    & (*e*) {in S &, forall xi phi : 'CF(L),
              orthogonal phi (xi :: xi^*%CF) -> orthogonal (R phi) (R xi)}].

(* This is Peterfalvi (5.2)(a). *)
Lemma irr_subcoherent (L G : {group gT}) S tau :
    [/\ uniq S, {subset S <= irr L} & conjC_closed S] ->
    {in 'Z[S, L^#], isometry tau, to 'Z[irr G, G^#]} ->
  {R | subcoherent S tau R}.
Proof.
move=> [U_S irrS clC_S] [isoL Ztau].
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

Section SubCoherentProperties.

Variables (L G : {group gT}) (S : seq 'CF(L)) (R : 'CF(L) -> seq 'CF(G)).
Variable tau : {linear 'CF(L) -> 'CF(G)}.
Hypothesis cohS : subcoherent S tau R.

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
by rewrite cfdot_subl cfdot_orthonormal ?subrr.
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
have [[ZS ccS] [tS Zt] oS /(_ _ Schi)[ZR onR tcc'] _] := cohS.
have [_ oSS] := pairwise_orthogonalP oS.
have /andP[ne_cc' /= Sc'] := ccS _ Schi.
have nzc: chi != 0 by apply: contraNneq ne_cc' => ->; rewrite raddf0.
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

Lemma conjC_pair_orthogonal S1 (chi : 'CF(L)) :
    conjC_closed S1 -> pairwise_orthogonal S1 -> chi \in S1 ->
  pairwise_orthogonal (chi :: chi^*%CF).
Proof.
move=> ccS1 /pairwise_orthogonalP[/andP[nzS1 _] oS1] S1chi; set S2 := _ :: _.
have /andP[ne_chi /= S1chi'] := ccS1 _ S1chi.
rewrite /orthogonal /= cfdotC oS1 // rmorph0 eqxx /=.
by move/negP: nzS1; do 2!case: eqP => [<- // | _].
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
  have [[_ ccS] _ oS _ _] := cohS.
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

Section MoreOrthogonal.

Variable H : {group gT}.

Lemma span_orthogonal S1 S2 phi1 phi2 :
    orthogonal S1 S2 -> phi1 \in span S1 -> phi2 \in span S2 ->
  '[phi1, phi2]_H = 0.
Proof.
move/orthogonalP=> oS12; do 2!move/(@coord_span _ _ _ (in_tuple _))->.
rewrite cfdot_suml big1 // => i _; rewrite cfdot_sumr big1 // => j _.
by rewrite cfdotZl cfdotZr oS12 ?mem_nth ?mulr0.
Qed.

Lemma cfproj_sum_orthogonal z S1 phi :
     pairwise_orthogonal S1 -> phi \in S1 ->
  '[\sum_(xi <- S1) z xi *: xi, phi]_H = z phi * '[phi].
Proof.
move=> oS1 /rot_to[i S2 defS2].
have defS1: perm_eq S1 (phi :: S2) by rewrite -(perm_rot i) defS2.
rewrite (eq_big_perm _ defS1) big_cons /= cfdotDl cfdotZl big_seq.
move: oS1; rewrite (eq_pairwise_orthogonal defS1) => /and3P[_ ophiS2 _].
rewrite addrC cfdotC (span_orthogonal ophiS2) ?rmorph0 ?add0r //.
  by rewrite memv_span ?mem_head.
by rewrite memv_suml // => xi S2xi; rewrite memvZl ?memv_span.
Qed.

Lemma cfdot_sum_orthogonal z1 z2 S1 :
     pairwise_orthogonal S1 ->
  '[\sum_(xi <- S1) z1 xi *: xi, \sum_(xi <- S1) z2 xi *: xi]_H
         = \sum_(xi <- S1) z1 xi * (z2 xi)^* * '[xi].
Proof.
move=> oS1; rewrite cfdot_sumr !big_seq; apply: eq_bigr => phi S1phi.
by rewrite -big_seq cfdotZr cfproj_sum_orthogonal // mulrCA mulrA.
Qed.

Lemma cfnorm_sum_orthogonal z S1 :
     pairwise_orthogonal S1 ->
  '[\sum_(xi <- S1) z xi *: xi]_H = \sum_(xi <- S1) `|z xi| ^+ 2 * '[xi].
Proof.
by move/cfdot_sum_orthogonal=> -> //; apply: eq_bigr => xi _; rewrite normCK.
Qed.

Lemma nth_index_map (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) x0 x :
  {in s &, injective f} -> x \in s -> nth x0 s (index (f x) (map f s)) = x.
Proof.
elim: s => //= y s IHs inj_f s_x; rewrite (inj_in_eq inj_f) ?mem_head //.
move: s_x; rewrite inE eq_sym; case: eqP => [-> | _] //=; apply: IHs.
by apply: sub_in2 inj_f => z; exact: predU1r.
Qed.

Lemma cfnormDd phi psi : '[phi, psi]_H = 0 -> '[phi + psi] = '[phi] + '[psi].
Proof. by move=> ophipsi; rewrite cfnormD ophipsi rmorph0 !addr0. Qed.

Lemma cfnorm_subd phi psi : '[phi, psi]_H = 0 -> '[phi - psi] = '[phi] + '[psi].
Proof.
by move=> ophipsi; rewrite cfnormDd ?cfnormN // cfdotNr ophipsi oppr0.
Qed.

Lemma sub_pairwise_orthogonal (S1 S2 : seq 'CF(H)) :
    {subset S1 <= S2} ->  uniq S1 ->
  pairwise_orthogonal S2 -> pairwise_orthogonal S1.
Proof.
move=> sS12 uniqS1 /pairwise_orthogonalP[/andP[notS2_0 _] oS2].
apply/pairwise_orthogonalP; rewrite /= (contra (sS12 0)) //.
by split=> //; exact: sub_in2 oS2.
Qed.

Lemma sub_orthonormal (S1 S2 : seq 'CF(H)) :
  {subset S1 <= S2} -> uniq S1 -> orthonormal S2 -> orthonormal S1.
Proof.
move=> sS12 uniqS1 /orthonormalP[_ oS1]. 
by apply/orthonormalP; split; last exact: sub_in2 sS12 _ _.
Qed.

Lemma vcharD1E (phi : 'CF(H)) S1 :
  (phi \in 'Z[S1, H^#]) = (phi \in 'Z[S1]) && (phi 1%g == 0).
Proof. by rewrite vchar_split cfunD1E. Qed.

Lemma sub_refl {T} {mD : mem_pred T} : sub_mem mD mD. Proof. by []. Qed.

Lemma sub_iso_to (mD1 mD2 : mem_pred 'CF(H)) (mR1 mR2 : mem_pred 'CF(G)) tau1:
    sub_mem mD2 mD1 -> sub_mem mR1 mR2 ->
  isometry_from_to mD1 tau1 mR1 -> isometry_from_to mD2 tau1 mR2.
Proof.
by move=> sD sR [Itau Rtau]; split=> [|u /sD/Rtau/sR //]; exact: sub_in2 Itau.
Qed.

Lemma map_of_seq (aT : eqType) rT (As : seq aT) (Rs : seq rT) (y0 : rT) :
  {f | uniq As -> size Rs = size As -> map f As = Rs}.
Proof.
exists (fun x => nth y0 Rs (index x As)) => uAs eq_sz.
apply/esym/(@eq_from_nth _ y0); rewrite ?size_map eq_sz // => i ltiAs.
have x0 : aT by [case: (As) ltiAs]; by rewrite (nth_map x0) // index_uniq.
Qed.

Lemma linear_of_free (F : fieldType) (V : vectType F) (W : lmodType F)
                      (B : seq V) (fB : seq W) :
  {f : {linear V -> W} | free B -> size fB = size B -> map f B = fB}.
Proof.
pose f u := \sum_i coord (in_tuple B) u i *: fB`_i.
have lin_f: linear f.
  move=> k u v; rewrite scaler_sumr -big_split; apply: eq_bigr => i _.
  by rewrite /= scalerA -scaler_addl linearP !ffunE.
exists (Linear lin_f) => freeB eq_sz.
apply/esym/(@eq_from_nth _ 0); rewrite ?size_map eq_sz // => i ltiB.
rewrite (nth_map 0) //= /f (bigD1 (Ordinal ltiB)) //=.
rewrite big1 => [|j /negbTE neqji]; rewrite (free_coordt (Ordinal _)) //.
  by rewrite eqxx scale1r addr0.
by rewrite eq_sym neqji scale0r.
Qed. 

Definition cfnorm := [fun phi => '[phi]_H].

End MoreOrthogonal.

Implicit Arguments cfnorm [H].

Lemma big_index_uniq T I idx (op : Monoid.com_law idx) r
                     (E : 'I_(size r) -> T) :
    @uniq I r ->
  \big[op/idx]_i E i = \big[op/idx]_(x <- r) oapp E idx (insub (index x r)).
Proof.
move=> Ur; apply/esym; rewrite big_tnth; apply: eq_bigr => i _.
by rewrite index_uniq // valK.
Qed.

Section Rem.

Variables (T : eqType) (x : T).

Fixpoint rem s := if s is y :: t then (if y == x then t else y :: rem t) else s.

Lemma rem_id s : x \notin s -> rem s = s.
Proof.
by elim: s => //= y s IHs /norP[neq_yx /IHs->]; rewrite eq_sym (negbTE neq_yx).
Qed.

Lemma perm_to_rem s : x \in s -> perm_eq s (x :: rem s).
Proof.
elim: s => // y s IHs; rewrite inE /= eq_sym perm_eq_sym.
case: eqP => [-> // | _ /IHs].
by rewrite (perm_catCA [:: x] [:: y]) perm_cons perm_eq_sym.
Qed.

Lemma size_rem s : x \in s -> size (rem s) = (size s).-1.
Proof. by move/perm_to_rem/perm_eq_size->. Qed.

Lemma rem_subseq s : subseq (rem s) s.
Proof.
elim: s => //= y s IHs; rewrite eq_sym.
by case: ifP => _; [exact: subseq_cons | rewrite eqxx].
Qed.

Lemma rem_filter s : uniq s -> rem s = filter (predC1 x) s.
Proof.
elim: s => //= y s IHs /andP[not_s_y /IHs->].
by case: eqP => //= <-; apply/esym/all_filterP; rewrite all_predC has_pred1.
Qed.

End Rem.

Lemma big_rem T (idx : T) (op : Monoid.com_law idx)
                 (I : eqType) r x (P : pred I) E:
     x \in r ->
  \big[op/idx]_(y <- r | P y) E y
     = op (if P x then E x else idx) (\big[op/idx]_(y <- rem x r | P y) E y).
Proof.
by move/perm_to_rem/(eq_big_perm _)->; rewrite !(big_mkcond P) big_cons.
Qed.

Implicit Arguments big_rem [T idx op I r P E].

Lemma isometry_of_cfnorm S1 S2 :
    pairwise_orthogonal S1 -> pairwise_orthogonal S2 ->
    map cfnorm S1 = map cfnorm S2 ->
  {tau : {linear 'CF(L) -> 'CF(G)} | map tau S1 = S2
       & {in span S1 &, isometry tau}}.
Proof.
move=> oS1 oS2 eq_nS12; have freeS1 := orthogonal_free oS1.
have eq_sz: size S2 = size S1 by have:= congr1 size eq_nS12; rewrite !size_map.
have [tau1 /(_ freeS1 eq_sz) defS2] := linear_of_free S1 S2.
rewrite -[S1]/(tval (in_tuple S1)).
exists tau1 => // u v /coord_span-> /coord_span->; rewrite !raddf_sum /=.
apply: eq_bigr => i _ /=; rewrite linearZ !cfdotZr !cfdot_suml; congr (_ * _).
apply: eq_bigr => j _ /=; rewrite linearZ !cfdotZl; congr (_ * _).
rewrite -!((nth_map _ 0) tau1) // defS2; have [-> | neq_ji] := eqVneq j i.
  by rewrite -!['[_]]((nth_map _ 0) cfnorm) ?eq_sz // eq_nS12.
have{oS1} [/=/andP[_ uS1] oS1] := pairwise_orthogonalP oS1.
have{oS2} [/=/andP[_ uS2] oS2] := pairwise_orthogonalP oS2.
by rewrite oS1 ?oS2 ?mem_nth ? nth_uniq ?eq_sz.
Qed.

Lemma Zisometry_of_cfnorm S1 S2 :
    pairwise_orthogonal S1 -> pairwise_orthogonal S2 ->
    map cfnorm S1 = map cfnorm S2 -> {subset S2 <= 'Z[irr G]} ->
  {tau : {linear 'CF(L) -> 'CF(G)} | map tau S1 = S2
       & {in 'Z[S1], isometry tau, to 'Z[irr G]}}.
Proof.
move=> eq_nS12 oS1 oS2 Z_S2.
have [tau1 defS2 Itau1] := isometry_of_cfnorm eq_nS12 oS1 oS2.
exists tau1 => //; split; first exact: (sub_in2 (@vchar_span _ _ S1 _)).
move=> _ /vchar_expansion[z Zz ->].
rewrite big_seq linear_sum sum_vchar // => xi S1xi.
by rewrite linearZ scale_vchar ?Z_S2 // -defS2 map_f.
Qed.

Lemma subset_subcoherent S1 :
  [/\ uniq S1, {subset S1 <= S} & conjC_closed S1] -> subcoherent S1 tau R.
Proof.
case=> uS1 sS1 ccS1; have [[N_S _] Itau oS defR oR] := cohS.
split; last 1 [exact: sub_in1 defR | exact: sub_in2 oR].
- by split=> //; apply/allP=> xi /sS1/(allP N_S).
- apply: sub_iso_to Itau => //; apply: vchar_subset => //.
  exact: orthogonal_free.
exact: sub_pairwise_orthogonal oS.
Qed.

Lemma isometry_inj mD (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    prop_in2 mD (inPhantom (isometry tau1)) ->
    prop_in2 mD (inPhantom (forall u v, in_mem (u - v) mD)) ->
  prop_in2 mD (inPhantom (injective tau1)).
Proof.
move=> Itau lin_mD u v Du Dv /eqP; rewrite -subr_eq0 -raddf_sub -cfnorm_eq0.
by rewrite Itau ?lin_mD // cfnorm_eq0 subr_eq0 => /eqP.
Qed.

Lemma Zisometry_inj S1 A (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    {in 'Z[S1, A] &, isometry tau1} -> {in 'Z[S1, A] &, injective tau1}.
Proof. by move/isometry_inj; apply; exact: sub_vchar. Qed.

Lemma memPn (T : eqType) (D : pred T) x :
  reflect {in D, forall y, y != x} (x \notin D).
Proof.
apply: (iffP idP) => [notDx y | notDx]; first by apply: contraTneq => ->.
by apply/negP=> /notDx/eqP[].
Qed.
Implicit Arguments memPn [T D x].

Lemma map_pairwise_orthogonal S1 (tau1 : {additive 'CF(L) -> 'CF(G)}) :
    {in 'Z[S1] &, isometry tau1} ->
  pairwise_orthogonal S1 -> pairwise_orthogonal (map tau1 S1).
Proof.
move=> Itau1 oS1; have freeS1 := orthogonal_free oS1.
apply/pairwise_orthogonalP; have{oS1} [uS1 oS1] := pairwise_orthogonalP oS1.
have inj_tau1: {in 0 :: S1 &, injective tau1}.
  apply: sub_in2 (Zisometry_inj Itau1) => xi.
  by case/predU1P=> [-> | /mem_vchar->]; rewrite ?cfun0_vchar.
split; first by rewrite -(map_inj_in_uniq inj_tau1) /= raddf0 in uS1.
move=> _ _ /mapP[xi1 S1xi1 ->] /mapP[xi2 S1xi2 ->] neq_tau_xi.
by rewrite Itau1 ?mem_vchar ?oS1 //; apply: contraNneq  neq_tau_xi => ->.
Qed.

Lemma map_orthonormal S1 (tau1 : {additive 'CF(L) -> 'CF(G)}) :
  {in 'Z[S1] &, isometry tau1} -> orthonormal S1 -> orthonormal (map tau1 S1).
Proof.
move=> Itau1 /andP[nS1 oS1]; have freeS1 := orthogonal_free oS1.
apply/andP; split; last exact: map_pairwise_orthogonal.
apply/allP=> _ /mapP[xi S1xi -> /=]; rewrite Itau1 ?mem_vchar //.
exact: (allP nS1).
Qed.

(* This is Peterfalvi (5.6). *)
Lemma extend_coherent S1 xi1 chi :
    [/\ uniq S1, {subset S1 <= S} & conjC_closed S1] -> 
    [&& xi1 \in S1, chi \in S  & chi \notin S1] ->
    [/\ (*a*) coherent S1 L^# tau,
        (*b*) isNatC (chi 1%g / xi1 1%g)
      & (*c*) 2%:R * chi 1%g * xi1 1%g < \sum_(xi <- S1) xi 1%g ^+ 2 / '[xi]]
  -> coherent (chi :: chi^*%CF :: S1) L^# tau.
Proof.
move=> [uniqS1 sS1S ccS1] /and3P[S1xi1 Schi notS1chi].
case=> [[_ [t1 [iso_t1 Zt1] eq_t1_tau]] /isNatCP[a def_a] ub_chi1].
have [[/allP N_S ccS] [iso_tau Ztau] oS R_P oR] := cohS.
have [ZRchi onRchi sumRchi] := R_P _ Schi.
have ocS1 xi: xi \in S1 -> '[chi, xi] = 0.
  move=> S1xi; have [_ -> //] := pairwise_orthogonalP oS; first exact: sS1S.
  by apply: contraNneq notS1chi => ->.
have /memPn/= nzS := conjC_closed_not0 ccS.
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
  have /andP[/= _ S1xic] := ccS1 _ S1xi.
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
  rewrite /orthogonal /= !cfdotZr ocS1 // cfdotC conj_cfdot cfConjCK.
  by rewrite cfdotC ocS1 ?rmorph0 ?mulr0 ?eqxx //; case/ccS1/andP: S1xi1.
- set V3 := 'Z[_]; suffices sV3: {subset V3 <= 'Z[S, L^#]}.
    by split; [exact: sub_in2 iso_tau | move=> theta /sV3/Ztau/vcharW].
  move=> _ /vchar_expansion[z Zz ->]; rewrite big_cons big_seq1.
  rewrite add_vchar ?scale_vchar // vchar_split cfunD1E.
  rewrite sub_vchar ?mem_vchar //=; last by case/ccS/andP: Schi.
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
  rewrite -2!addrA oppr_add addNKr cfnormZ int_normCK // posC_opp.
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
have /andP[/= neq_cc' Sc'] := ccS _ Schi.
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
  rewrite /= -cat1s orthogonal_catr -!cfnorm_eq0 nX nXc.
  rewrite -conj_cfdot conjC_eq0 cfnorm_eq0 nzS //=.
  by rewrite {1}/orthogonal /= oXXc eqxx /= !oRchiX1.
have sS3S: {subset S3 <= S} by apply/allP; rewrite /= Schi Sc'; exact/allP.
have uniqS3: uniq S3.
  rewrite /= inE negb_or eq_sym neq_cc' notS1chi (contra _ notS1chi) //.
  by case/ccS1/andP=> _; rewrite cfConjCK.
have oS3: pairwise_orthogonal S3 by exact: sub_pairwise_orthogonal oS.
have nX3: map cfnorm S3 = map cfnorm X3.
  rewrite /= nX nXc -map_comp; congr [:: _, _ & _].
  by apply: eq_in_map => xi /= S1xi; rewrite iso_t1 ?Z_S1.
have Z_X3: {subset X3 <= 'Z[irr G]}.
  apply/allP; rewrite /= !(vchar_trans ZRchi) //.
  by apply/allP=> _ /mapP[xi S1xi ->]; rewrite Zt1 ?Z_S1. 
have [t3 defX3 iso_t3] := Zisometry_of_cfnorm oS3 oX3 nX3 Z_X3.
have [t3chi t3chi' t3S1] := defX3; rewrite -/(map t3 _) in t3S1.
split.
  exists (chi - chi^*%CF); last by rewrite subr_eq0 eq_sym.
  rewrite vchar_split (vchar_on Zcc').
  by rewrite sub_vchar // mem_vchar ?orthogonal_free ?inE ?eqxx ?orbT.
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

End SubCoherentProperties.


End Five.