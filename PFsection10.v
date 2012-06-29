(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection7 PFsection8 PFsection9.

(******************************************************************************)
(* This file covers Peterfalvi, Section 10: Maximal subgroups of Types III,   *)
(* IV and V. Defined here:                                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.

Section MoreStuff.

Lemma odd_prime_gt2 p : odd p -> prime p -> (p > 2)%N.
Proof.
by move=> odd_p p_pr; rewrite ltn_neqAle prime_gt1 //; case: eqP odd_p => // <-.
Qed.

Local Open Scope ring_scope.

Section Num.
Context {R : numDomainType}.

Lemma ler_sqr : {in Num.nneg &, {mono (fun x : R => x ^+ 2) : x y / x <= y}}.
Proof. exact: ler_pexpn2r. Qed.
Lemma ltr_sqr : {in Num.nneg &, {mono (fun x : R => x ^+ 2) : x y / x < y}}.
Proof. exact: ltr_pexpn2r. Qed.
End Num.

Section Vector.

Variables (F : fieldType) (vT : vectType F).
Import Vector.InternalTheory.

Lemma coord0 i (v : vT) : coord [tuple 0] i v = 0.
Proof.
rewrite unlock /pinvmx rank_rV; case: negP => [[] | _].
  by apply/eqP/rowP=> j; rewrite !mxE (tnth_nth 0) /= linear0 mxE.
by rewrite pid_mx_0 !(mulmx0, mul0mx) mxE.
Qed.

End Vector.

Section AlgC.

Lemma sqrtC_gt0 x : (sqrtC x > 0) = (x > 0).
Proof. by rewrite !ltr_def sqrtC_eq0 sqrtC_ge0. Qed.
Lemma ler_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x <= y}}.
Proof. by move=> x y ? ?; rewrite /= -ler_sqr ?sqrtCK ?qualifE ?sqrtC_ge0. Qed.
Lemma ltr_sqrtC : {in Num.nneg &, {mono sqrtC : x y / x < y}}.
Proof. by move=> x y ? ?; rewrite /= -ltr_sqr ?sqrtCK ?qualifE ?sqrtC_ge0. Qed.
Lemma sqrtCM : {in Num.nneg &, {morph sqrtC : x y / x * y}}.
Proof.
move=> x y x_ge0 y_ge0; rewrite /= -{1}[x]sqrtCK -{1}[y]sqrtCK -exprMn.
by rewrite sqrCK ?mulr_ge0 ?sqrtC_ge0.
Qed.

Lemma algIm_eq0 z : ('Im z == 0) = (z \is Creal).
Proof.
rewrite mulf_eq0 invr_eq0 orbC mulrn_eq0 (negPf algCi_neq0) /=.
by rewrite /= subr_eq0 eq_sym -CrealE.
Qed.
Lemma algRe_idP z : reflect ('Re z = z) (z \in Creal).
Proof.
rewrite -algIm_eq0 -(inj_eq (mulfI algCi_neq0)) -(inj_eq (addrI ('Re z))).
by rewrite -algCrect eq_sym mulr0 addr0; apply: eqP.
Qed.
Lemma conjC_rect : {in Creal &, forall x y, (x + 'i * y)^* = x - 'i * y}.
Proof.
by move=> x y Rx Ry; rewrite /= rmorphD rmorphM conjCi mulNr !conj_Creal.
Qed.
Lemma addC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) + (x2 + 'i * y2) = x1 + x2 + 'i * (y1 + y2).
Proof. by rewrite addrACA -mulrDr. Qed.
Lemma oppC_rect x y : - (x + 'i * y)  = - x + 'i * (- y).
Proof. by rewrite mulrN -opprD. Qed.
Lemma subC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) - (x2 + 'i * y2) = x1 - x2 + 'i * (y1 - y2).
Proof. by rewrite oppC_rect addC_rect. Qed.
Lemma mulC_rect x1 y1 x2 y2 :
  (x1 + 'i * y1) * (x2 + 'i * y2)
      = x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
Proof.
rewrite mulrDl 2!mulrDr mulrCA -!addrA mulrAC -mulrA; congr (_ + _).
by rewrite addrA -mulrDr addrC mulrACA -expr2 sqr_algCi mulN1r.
Qed.
Lemma invC_rect :
  {in Creal &, forall x y, (x + 'i * y)^-1  = (x - 'i * y) / (x ^+ 2 + y ^+ 2)}.
Proof.
move=> x y Rx Ry; rewrite /= invC_norm conjC_rect // mulrC.
by rewrite normC_rect // sqrtCK.
Qed.

Lemma normC_Re_Im z : `|z| = sqrtC ('Re z ^+ 2 + 'Im z ^+ 2).
Proof. by rewrite -normC_rect ?Creal_Re ?Creal_Im -?algCrect. Qed.

Lemma lerif_normC_Re_Creal z : `|'Re z| <= `|z| ?= iff (z \is Creal).
Proof.
rewrite -(mono_in_lerif ler_sqr); try by rewrite qualifE normr_ge0.
rewrite normCK conj_Creal ?Creal_Re // normC_Re_Im sqrtCK -expr2.
rewrite addrC -lerif_subLR subrr -algIm_eq0 -sqrf_eq0 eq_sym.
by apply: lerif_eq; rewrite -realEsqr Creal_Im.
Qed.

Lemma lerif_Re_Creal z : 'Re z <= `|z| ?= iff (0 <= z).
Proof.
have ubRe: 'Re z <= `|'Re z| ?= iff (0 <= 'Re z).
  by rewrite ger0_def eq_sym; apply/lerif_eq/real_ler_norm/Creal_Re.
congr (_ <= _ ?= iff _): (lerif_trans ubRe (lerif_normC_Re_Creal z)).
apply/andP/idP=> [[xRge0 /algRe_idP <- //] | x_ge0].
by have Rx := ger0_real x_ge0; rewrite (algRe_idP _ _).
Qed.

End AlgC.

Section Cfun.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type phi : 'CF(G).

Lemma cfnorm_gt0 phi : ('[phi] > 0) = (phi != 0).
Proof. by rewrite ltr_def cfnorm_ge0 cfnorm_eq0 andbT. Qed.

Lemma sqrt_cfnorm_ge0 phi : 0 <= sqrtC '[phi].
Proof. by rewrite sqrtC_ge0 cfnorm_ge0. Qed.
Lemma sqrt_cfnorm_eq0 phi : (sqrtC '[phi] == 0) = (phi == 0).
Proof. by rewrite sqrtC_eq0 cfnorm_eq0. Qed.
Lemma sqrt_cfnorm_gt0 phi : (sqrtC '[phi] > 0) = (phi != 0).
Proof. by rewrite sqrtC_gt0 cfnorm_gt0. Qed.

Lemma cfCauchySchwarz phi psi :
  `|'[phi, psi]| ^+ 2 <= '[phi] * '[psi] ?= iff ~~ free (phi :: psi).
Proof.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_psi] /= := altP (psi =P 0).
  by apply/lerifP; rewrite !cfdot0r normCK mul0r mulr0.
without loss ophi: phi / '[phi, psi] = 0.
  move=> IHo; pose a := '[phi, psi] / '[psi]; pose phi1 := phi - a *: psi.
  have ophi: '[phi1, psi] = 0.
    by rewrite cfdotBl cfdotZl divfK ?cfnorm_eq0 ?subrr.
  rewrite (canRL (subrK _) (erefl phi1)) rpredDr ?rpredZ ?memv_line //.
  rewrite cfdotDl ophi add0r cfdotZl normrM (ger0_norm (cfnorm_ge0 _)).
  rewrite exprMn mulrA -cfnormZ cfnormDd; last by rewrite cfdotZr ophi mulr0.
  by have:= IHo _ ophi; rewrite mulrDl -lerif_subLR subrr ophi normCK mul0r.
rewrite ophi normCK mul0r; split; first by rewrite mulr_ge0 ?cfnorm_ge0.
rewrite eq_sym mulf_eq0 orbC cfnorm_eq0 (negPf nz_psi) /=.
apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite cfdotZr ophi mulr0.
by rewrite cfnorm_eq0 => /eqP->; apply: rpred0.
Qed.

Lemma cfCauchySchwarz_sqrt phi psi :
  `|'[phi, psi]| <= sqrtC '[phi] * sqrtC '[psi] ?= iff ~~ free (phi :: psi).
Proof.
rewrite -(sqrCK (normr_ge0 _)) -sqrtCM ?qualifE ?cfnorm_ge0 //.
rewrite (mono_in_lerif ler_sqrtC) 1?rpredM ?qualifE ?normr_ge0 ?cfnorm_ge0 //.
exact: cfCauchySchwarz.
Qed.

Lemma cf_triangle_lerif phi psi :
  sqrtC '[phi + psi] <= sqrtC '[phi] + sqrtC '[psi]
           ?= iff ~~ free (phi :: psi) && (0 <= coord [tuple psi] 0 phi).
Proof.
rewrite -(mono_in_lerif ler_sqr) ?rpredD ?qualifE ?sqrtC_ge0 ?cfnorm_ge0 //.
rewrite andbC sqrrD !sqrtCK addrAC cfnormD (mono_lerif (ler_add2l _)).
rewrite -mulr_natr -[_ + _](divfK (negbT (eqC_nat 2 0))) -/('Re _).
rewrite (mono_lerif (ler_pmul2r _)) ?ltr0n //.
have:= lerif_trans (lerif_Re_Creal '[phi, psi]) (cfCauchySchwarz_sqrt phi psi).
congr (_ <= _ ?= iff _); apply: andb_id2r.
rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC.
have [-> | nz_psi] := altP (psi =P 0); first by rewrite cfdot0r coord0.
case/vlineP=> [x ->]; rewrite cfdotZl linearZ pmulr_lge0 ?cfnorm_gt0 //=.
by rewrite (coord_free 0) ?seq1_free // eqxx mulr1.
Qed.

End Cfun.

End MoreStuff.

Section Ten.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U W : {group gT}.

Section OneMaximal.

(* These assumptions correspond to Peterfalvi, Hypothesis (10.1).             *)
(* We also declare the group U, even though it is not used in this sections,  *)
(* because it is a parameter to the theorems and definitions of PFsection8    *)
(* and PFsection9.                                                            *)
Variables M U W1 : {group gT}.
Hypotheses (maxM : M \in 'M) (MtypeP : of_typeP M U W1).
Hypothesis (notMtype2: FTtype M != 2).

Local Notation "` 'M'" := (gval M) (at level 0, only parsing) : group_scope.
Local Notation "` 'W1'" := (gval W1) (at level 0, only parsing) : group_scope.
Local Notation W2 := 'C_(`M`_\F)(`W1)%G.
Local Notation "` 'W2'" := 'C_(`M`_\F)(`W1) : group_scope.
Local Notation W := (`W1 <*> `W2)%G.
Local Notation "` 'W'" := (`W1 <*> `W2) : group_scope.
Local Notation V := (`W :\: (`W1 :|: `W2)).
Local Notation M' := M^`(1)%G.
Local Notation "` 'M''" := `M^`(1) (at level 0) : group_scope.
Local Notation M'' := M^`(2)%G.
Local Notation "` 'M'''" := `M^`(2) (at level 0) : group_scope.

Let defM : M' ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let notMtype1 : FTtype M != 1%N. Proof. exact: FTtypeP_neq1 MtypeP. Qed.

Let cddM := FTs_cDade_hyp maxM MtypeP.

Let w1 := #|W1|.
Let w2 := #|W2|.

Local Open Scope ring_scope.

Let sigma := (@cyclicTIsigma _ [set: _] W W1 W2).
Let w_ i j := (@cyclicTIirr _ W W1 W2 i j).
Let Imu2_ i j := (@Dade_mu2 _ M W W1 W2 i j).
Local Notation mu2_ i j := 'chi_(Imu2_ i j).
Let mu_ j := (@Dade_mu _ M W W1 W2 j).
Let Edelta_ j := (@Dade_delta _ M W W1 W2 j).
Local Notation delta_ j := ((-1) ^+ Edelta_ j : algC).
Local Notation delta__ j := ((-1) ^+ nat_of_bool (Edelta_ j)).

Local Notation tau := (FT_Dade0 maxM).
Local Notation "chi ^\tau" := (tau chi).

Let defMs : M`_\s :=: M'.
Proof.
by rewrite /M`_\s -(mem_iota 1 2) !inE (negPf notMtype1) (negPf notMtype2).
Qed.

Let calS := seqIndD M' M M' 1.
Let rmR := FTtypeP_coh_base maxM MtypeP.
Let scohM : subcoherent calS tau rmR.
Proof.
by have:= FTtypeP_subcoherent maxM MtypeP; rewrite (group_inj defMs).
Qed.

Let nsM''M' : M'' <| M'. Proof. exact: (der_normal 1 M'). Qed.
Let nsM'M : M' <| M. Proof. exact: (der_normal 1 M). Qed.
Let sM'M : M' \subset M. Proof. exact: der_sub. Qed.

(* This is Peterfalvi (10.2). *)
Lemma FTtype345_ref_irr : {t : Iirr M | 'chi_t \in calS & 'chi_t 1%g = w1%:R}.
Proof.
have nsM''M: M'' <| M := der_normal 2 M.
have frobMbar: [Frobenius M / M'' = (M' / M'') ><| (W1 / M'')].
  have [[_ hallW1 ntW1 _] _ _ [_ ntW2 _ sW2M'' regM'W1 ] _] := MtypeP.
  apply: Frobenius_coprime_quotient => //.
    by rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM).
  split=> [|w /regM'W1-> //]; apply: (sol_der1_proper (mmax_sol maxM)) => //.
  by apply: subG1_contra ntW2; apply: subset_trans sW2M'' (der_sub 1 M').
have [_ ntM'bar _ _ _] := Frobenius_context frobMbar.
have [s nz_s] := has_nonprincipal_irr ntM'bar.
have /irrP/sig_eqW[t Dt]: 'Ind[M / M''] 'chi_s \in irr (M / M'').
  exact: irr_induced_Frobenius_ker (FrobeniusWker frobMbar) s nz_s.
exists (mod_Iirr t); rewrite mod_IirrE //= -Dt -cfIndMod ?normal_sub //.
  rewrite  -mod_IirrE // mem_seqInd ?normal1 //.
  by rewrite!inE sub1G subGcfker mod_Iirr_eq0 ?nz_s.
rewrite cfInd1 ?der_sub // -(index_sdprod defM) -/w1 lin_char1 ?mulr1 //.
by rewrite -mod_IirrE // lin_irr_der1 mod_IirrE ?cfker_mod.
Qed.
Let zeta := 'chi_(s2val FTtype345_ref_irr).
Let Szeta : zeta \in calS. Proof. exact: (s2valP FTtype345_ref_irr). Qed.
Let zeta1w1 : zeta 1%g = w1%:R. Proof. exact: (s2valP' FTtype345_ref_irr). Qed.

(* This is Peterfalvi (10.3), first assertion. *)
Lemma FTtype345_core_prime : prime w2.
Proof.
case: ifP (FT_FPstructure gT) => [/forall_inP/(_ M maxM)/idPn[] // | _].
case=> sW sW1 sW2 S T strST.
without loss [x defMx]: sW sW1 sW2 S T strST / exists x, M :=: T :^ x.
  have [_ _ _ _ /(_ M)[]// x [] defMx IH_ST] := strST.
    by apply: IH_ST (FT_Pstructure_sym strST) _; exists x.
  by apply: IH_ST strST _; exists x.
have typeT_M: FTtype T = FTtype M by rewrite defMx FTtypeJ.
have [[_ maxS maxT] [defS defT _] /orP Stype2 _ _] := strST.
rewrite orbC typeT_M {1}(negPf notMtype2) /= in Stype2.
move: defM; rewrite /w2 /= defMx derJ -(conjsgKV x W1) -sdprodJ.
move/act_inj=> defTx; rewrite FcoreJ centJ -conjIg cardJg.
have{typeT_M} notTtype1: FTtype T != 1%N by rewrite typeT_M.
have{defT} [Us PtypeTs] := compl_of_typeP defT maxT notTtype1.
have{defTx maxT notTtype1} [Ux PtypeTx] := compl_of_typeP defTx maxT notTtype1.
have{Us PtypeTs Ux PtypeTx} [y [Ty _ ->]] := of_typeP_conj PtypeTx PtypeTs.
rewrite -{Ty}(normsP (normal_norm (Fcore_normal T)) y Ty) centJ -conjIg.
rewrite {y}cardJg (def_cycTIcompl (FT_Pstructure_sym strST)).
have notStype1: FTtype S != 1%N by rewrite (eqP Stype2).
have [Us PtypeS] := compl_of_typeP defS maxS notStype1.
by have [[]] := compl_of_typeII PtypeS maxS Stype2.
Qed.
Local Notation w2_pr := FTtype345_core_prime.
Hint Resolve w2_pr.
Let w2_gt0 : (w2 > 0)%N. Proof. exact: prime_gt0. Qed.
Let w2_gt1 : (w2 > 1)%N. Proof. exact: prime_gt1. Qed.

Definition FTtype345_mu_degree := truncC (mu2_ 0 (inord 1) 1%g).
Definition FTtype345_mu_sign := delta_ (inord 1).
Local Notation d := FTtype345_mu_degree.
Local Notation delta := FTtype345_mu_sign.
Definition FTtype345_reduced_mu_degree := (d%:R - delta) / w1%:R.
Local Notation n := FTtype345_reduced_mu_degree.

Let cTImu : cyclicTIhypothesis M W W1 W2 := cyclicTI_Dade cddM.
Local Notation defW := (cyclicTIhyp_W1xW2 cTImu).
Local Notation sig_mu := (cyclicTIsigma M W W1 W2).

(* This should go in Section 4. *)
Let Dade_mu2_degree i j : mu2_ i j 1%g = mu2_ 0 j 1%g.
Proof. by rewrite -!(@cfRes1 _ M' M) (Dade_chi_eq cddM). Qed.

Let Dade_mu2_degree0 i : mu2_ i 0 1%g = 1.
Proof. by rewrite Dade_mu2_degree [Imu2_ 0 0](Dade_mu20 cddM) irr0 cfun11. Qed.

Let Dade_mu20_linear i : mu2_ i 0 \is a linear_char.
Proof. by rewrite qualifE irr_char /= Dade_mu2_degree0. Qed.

(* This is the remainder of Peterfalvi (10.3). *)
Lemma FTtype345_invariants :
  [/\ forall i j, j != 0 -> mu2_ i j 1%g = d%:R,
      forall j, j != 0 -> delta_ j = delta,
      (d > 1)%N
    & n \in Cnat].
Proof.
pose j1 : Iirr W2 := inord 1.
have [_ _ _ [cycW2 _ _ _ _] _] := MtypeP; have abW2 := cyclic_abelian cycW2.
have val_j1: j1 = 1%N :> nat.
  by rewrite inordK // -[Nirr _]card_ord card_Iirr_abelian.
have nz_j1 : j1 != 0 by rewrite -val_eqE /= val_j1.
have invj j: j != 0 -> mu2_ 0 j 1%g = d%:R /\ delta_ j = delta.
  have [lW2 [cF [inj_cF lin_cF onto_cF]] [cF_M cF_1 _]] := lin_char_group W2.
  have /fin_all_exists[cF' cF'K] (k) := onto_cF _ (char_abelianP _ abW2 k).
  have cF_X m: {morph cF : xi / (xi ^+ m)%g >-> xi ^+ m}.
    by move=> xi; elim: m => // m IHm; rewrite expgS exprS cF_M IHm.
  have o_cF xi: #[xi]%g = #[cF xi]%CF.
    apply/eqP; rewrite eqn_dvd; apply/andP; split.
      by rewrite order_dvdn -(inj_eq inj_cF) cF_1 cF_X exp_cforder.
    by rewrite dvdn_cforder; rewrite -cF_X expg_order cF_1.
  have cforder_irr_eq1 k: (#['chi[W2]_k]%CF == 1%N) = (k == 0).
    by rewrite -dvdn1 dvdn_cforder irr_eq1.
  have cforder_lin_dvdG phi:
    phi \is a linear_char -> #[phi : 'CF(W2)]%CF %| #|W2|.
  - move=> Lphi; rewrite dvdn_cforder; apply/eqP/cfun_inP=> x Gx.
    rewrite cfun1E Gx exp_cfunE // -lin_charX // -(lin_char1 Lphi).
    by congr (phi _); apply/eqP; rewrite -order_dvdn order_dvdG.
  have o_cF' k: k != 0 -> #[cF' k] = w2.
    rewrite -cforder_irr_eq1 cF'K -o_cF => nt_cF'k.
    by apply/prime_nt_dvdP=> //; rewrite o_cF cforder_lin_dvdG.
  have o_lW2: #|[set: lW2]| = w2.
    rewrite -[w2]card_Iirr_abelian // cardsT -!sum1_card (reindex cF') //.
    exists (cfIirr \o cF) => [k | xi] _ /=; first by rewrite -cF'K irrK.
    by apply/inj_cF; rewrite -cF'K cfIirrE ?lin_char_irr.
  have gen_lW2 k: k != 0 -> generator [set: lW2] (cF' k).
    move=> /o_cF' o_cF'k; rewrite /generator eq_sym eqEcard subsetT /=.
    by rewrite o_lW2 -o_cF'k.
  have w_Er k: w_ 0 k = cfDprodr defW 'chi_k.
    by rewrite [w_ 0 k](cTIirrE cTImu) dprod_IirrE irr0 cfDprod_cfun1l.
  have oi0j1: #[w_ 0 j1]%CF = #['chi_j1]%CF.
    apply/eqP; rewrite w_Er eqn_dvd; apply/andP; split.
      apply/dvdn_cforderP=> _ /(mem_dprod defW)[x [y [W1x W2y -> _]]].
      by rewrite cfDprodEr //; apply/dvdn_cforderP.
    apply/dvdn_cforderP=> y W2y; rewrite -(cfDprodEr defW _ (group1 W1)) //.
    by apply/dvdn_cforderP; rewrite //= -(dprodW defW) mem_mulg.
  move/gen_lW2=> gen_j; have gen_j1 := (_ =P <[_]>) (gen_lW2 _ nz_j1).
  rewrite gen_j1 in gen_j; have /cycleP[m Dj] := cycle_generator gen_j.
  rewrite Dj generator_coprime o_cF -cF'K -oi0j1 coprime_sym in gen_j.
  have [[u]] := cyclicTI_aut_exists cTImu gen_j; rewrite -!['chi__]/(w_ _ _).
  rewrite {1}w_Er -rmorphX cF'K -cF_X -Dj -cF'K /= -w_Er => Dj1u _.
  rewrite truncCK ?Cnat_irr1 // -/j1.
  have: delta_ j *: mu2_ 0 j == cfAut u (delta_ j1 *: mu2_ 0 j1).
    by rewrite -!(Dade_mu2_sigma cddM) -/cTImu -Dj1u.
  rewrite raddfZsign /= -(Dade_mu2_aut cddM) eq_scaled_irr signr_eq0 /=.
  case/andP=> /eqP-> /eqP->; rewrite (Dade_mu2_aut cddM) cfunE.
  by rewrite aut_Cnat ?Cnat_irr1.
have d_gt1: (d > 1)%N.
  rewrite ltn_neqAle andbC -eqC_nat -ltC_nat truncCK ?Cnat_irr1 // -/j1.
  rewrite irr1_gt0 /= eq_sym; apply: contraNneq nz_j1 => mu2_lin.
  suffices: Imu2_ 0 j1 \in [set Imu2_ i 0 | i : Iirr W1].
    by case/imsetP=> i _ /(Dade_mu2_inj cddM)[_ ->].
  rewrite -(Dade_mu2_subset_cfker cddM) inE -lin_irr_der1 qualifE irr_char /=.
  by rewrite mu2_lin.
split=> // [i j /invj[<- _] | _ /invj[//] | ]; first by rewrite Dade_mu2_degree.
have: (d%:R == delta %[mod w1])%C.
  by rewrite truncCK ?Cnat_irr1 ?(Dade_mu2_mod cddM).
rewrite /eqCmod unfold_in -/n (negPf (neq0CG W1)) CnatEint => ->.
rewrite divr_ge0 ?ler0n // [delta]signrE opprB addrA -natrD subr_ge0 ler1n.
by rewrite -(subnKC d_gt1).
Qed.

Definition FTtype345_compensated_mu i j :=
  mu2_ i j - delta *: mu2_ i 0 - n *: zeta.
Local Notation alpha_ := FTtype345_compensated_mu.

Let coM'w1 : coprime #|M'| w1.
Proof.
by rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM); have [[]] := MtypeP.
Qed.

Let typeMgt2 : (FTtype M > 2)%N.
Proof.
rewrite 2!ltn_neqAle ?(eq_sym _.+1) notMtype1 notMtype2.
by have /andP[] := FTtype_range M.
Qed.

Let defA : 'A(M) = M'^#. Proof. by rewrite FTsupp_eq1 //= -FTcore_eq_der1. Qed.

(* This is the first part of Peterfalvi (10.5), which does not depend on the  *)
(* coherence assumption that will ultimately be falsified on (10.8).          *)
Lemma supp_FTtype345_compensated_mu i j :
  j != 0 -> alpha_ i j \in 'CF(M, 'A0(M)).
Proof.
move=> nz_j; have [Dd Ddelta _ _] := FTtype345_invariants.
have [Dmu2 _] := Dade_mu2_restrict cddM.
have W1a0 x: x \in W1 -> alpha_ i j x = 0.
  move=> W1x; rewrite !cfunE; have [-> | ntx] := eqVneq x 1%g.
    by rewrite Dd // Dade_mu2_degree0 mulr1 zeta1w1 divfK ?neq0CG ?subrr.
  have notM'x: x \notin M'.
    apply: contra ntx => M'x; have: x \in M' :&: W1 by exact/setIP.
    by rewrite coprime_TIg ?inE.
  have /sdprod_context[_ sW1W _ _ tiW21] := dprodWsdC defW.
  have abW2: abelian W2 by have [_ _ _ [/cyclic_abelian]] := MtypeP.
  have Wx: x \in W :\: W2.
    rewrite inE (contra _ ntx) ?(subsetP (joing_subl W1 W2)) // => W2x.
    by rewrite -in_set1 -set1gE -tiW21 inE W2x.
  rewrite !Dmu2 {Wx}// Ddelta // (Dade_delta0 cddM) scale1r !(cTIirrE cTImu).
  rewrite !dprod_IirrE cfunE -!(cfResE _ sW1W) ?cfDprodKl_abelian // subrr.
  have [s _ ->] := seqIndP Szeta.
  by rewrite (cfun_on0 (cfInd_normal _ _)) ?mulr0 ?subrr.
apply/cfun_onP=> x; rewrite !inE defA notMtype1 /= => /norP[notM'x].
set pi := \pi(M'); have [Mx /= pi_x | /cfun0->//] := boolP (x \in M).
have hallM': pi.-Hall(M) M' by rewrite Hall_pi -?(coprime_sdprod_Hall defM).
have hallW1: pi^'.-Hall(M) W1 by rewrite -(compl_pHall _ hallM') sdprod_compl.
have{pi_x} pi'x: pi^'.-elt x.
  apply: contraR notM'x => not_pi'x; rewrite !inE (mem_normal_Hall hallM') //.
  rewrite not_pi'x andbT negbK in pi_x.
  by rewrite (contraNneq _ not_pi'x) // => ->; apply: p_elt1.
have [|y My] := Hall_subJ (mmax_sol maxM) hallW1 _ pi'x; rewrite cycle_subG //.
by case/imsetP=> z Wz ->; rewrite cfunJ ?W1a0.
Qed.
Local Notation alpha_on := supp_FTtype345_compensated_mu.

Local Notation w_sig i j := (sigma (w_ i j)).

Let o_mu2_zeta i j : '[mu2_ i j, zeta] = 0.
Proof.
have [s _ Dzeta] := seqIndP Szeta.
rewrite Dzeta -cfdot_Res_l -(Dade_chiE cddM) cfdot_irr.
rewrite (negPf (contraNneq _ (Dade_mu_not_irr cddM j))) // => Ds.
by rewrite -(Dade_Ind_chi cddM) Ds -Dzeta mem_irr.
Qed.

Section NonCoherence.

(* We will ultimately contradict these assumptions. *)
(* Note that we do not need to export any lemma save the final contradiction. *)
Variable tau1 : {additive 'CF(M) -> 'CF(G)}.
Hypothesis cohS : coherent_with calS M^# tau tau1.

Local Notation "mu ^\tau1" := (tau1 mu%CF)
  (at level 2, format "mu ^\tau1") : ring_scope.

Let Dtau1 : {in 'Z[calS, M'^#], tau1 =1 tau}.
Proof. by case: cohS => _; apply: sub_in1; apply: zchar_onS; apply: setSD. Qed.

Let tauM' : {subset 'Z[calS, M'^#] <= 'CF(M, 'A0(M))}.
Proof. by rewrite -defA => phi /zchar_on/(cfun_onS (subsetUl _ _))->. Qed.

(* This is the second part of Peterfalvi (10.5). *)
Let tau_alpha i j : j != 0 ->
  (alpha_ i j)^\tau = delta *: (w_sig i j - w_sig i 0) - n *: zeta^\tau1.
Proof.
move=> nz_j; set al_ij := alpha_ i j; have [[Itau1 Ztau1] _] := cohS.
have [mu1 Ddelta d_gt1 Nn] := FTtype345_invariants.
have [[cycW1 _ ntW1 _] _ _ _ _] := MtypeP.
pose a := '[al_ij^\tau, zeta^\tau1] + n.
have Smu_ k: k != 0 -> mu_ k \in calS.
  rewrite /mu_ -(Dade_Ind_chi cddM) mem_seqInd ?normal1 // !inE sub1G andbT.
  rewrite subGcfker -irr_eq1 -(Dade_chi0 cddM) (inj_eq irr_inj).
  by rewrite (inj_eq (Dade_irr_inj cddM)).    
have al_ij_zeta_s: '[al_ij^\tau, zeta^*^\tau1] = a.
  apply: canRL (addNKr _) _; rewrite addrC -opprB -cfdotBr -raddfB.
  have M'dz: zeta - zeta^*%CF \in 'Z[calS, M'^#].
    exact: seqInd_sub_aut_zchar.
  rewrite Dtau1 // Dade_isometry ?alpha_on ?tauM' //.
  rewrite cfdotBr opprB cfdotBl cfdotC -cfdot_conjC cfConjCK cfdotC rmorphB.
  rewrite linearZ /= !cfdotBl !cfdotZl -!(Dade_mu2_aut cddM) !o_mu2_zeta.
  rewrite (seqInd_conjC_ortho _ _ _ Szeta) ?mFT_odd // cfnorm_irr !mulr0.
  by rewrite mulr1 opprB !(subr0, rmorph0) add0r.
have Zal_ij: al_ij^\tau \in 'Z[irr G].
  rewrite Dade_vchar // zchar_split alpha_on //.
  rewrite !rpredB ?rpredZnat ?rpredZsign ?irr_vchar //.
  by rewrite rpredZ_Cnat ?(seqInd_vcharW Szeta).
have Za: a \in Cint.
  by rewrite rpredD ?(Cint_Cnat Nn) ?Cint_cfdot_vchar ?Ztau1 ?(mem_zchar Szeta).
have nm_alij: '[al_ij^\tau] = 2%:R + n ^+ 2.
  rewrite Dade_isometry ?alpha_on // cfnormBd ?cfnormZ; last first.
    by rewrite cfdotZr cfdotBl cfdotZl !o_mu2_zeta !(mulr0, subr0).
  rewrite ger0_norm ?Cnat_ge0 // cfnormBd ?cfnorm_sign ?cfnorm_irr ?mulr1 //.
  rewrite cfdotZr cfdot_irr (negPf (contraNneq _ nz_j)) ?mulr0 //.
  by case/(Dade_mu2_inj cddM) => ->.
have{al_ij_zeta_s} ub_da2: (d ^ 2)%:R * a ^+ 2 <= (2%:R + n ^+ 2) * w1%:R.
  have [k nz_k j'k]: exists2 k, k != 0 & k != j.
    have: (2 < #|W2|)%N by rewrite odd_prime_gt2 ?mFT_odd.
    rewrite -card_Iirr_abelian ?cyclic_abelian ?prime_cyclic //.
    rewrite (cardD1 0) (cardD1 j) !inE nz_j !ltnS lt0n.
    by case/pred0Pn=> k /and3P[]; exists k.
  have muk_1: mu_ k 1%g = (d * w1)%:R.
    rewrite mulrnA /w1 -card_Iirr_abelian ?cyclic_abelian //.
    by rewrite sum_cfunE -sumr_const; apply: eq_bigr => i1 _; rewrite mu1.
  rewrite natrX -exprMn; have <-: '[al_ij^\tau, (mu_ k)^\tau1] = d%:R * a.
    rewrite mulrDr mulr_natl -raddfMn /=; apply: canRL (addNKr _) _.
    rewrite addrC -cfdotBr -raddfMn -raddfB -scaler_nat.
    have Smudz: mu_ k - d%:R *: zeta \in 'Z[calS, M'^#].
      rewrite -[d%:R](mulfK (neq0CG W1)) -natrM -muk_1 (index_sdprod defM).
      by rewrite (seqInd_sub_lin_vchar _ Szeta) ?Smu_ -?(index_sdprod defM).
    rewrite Dtau1 // Dade_isometry ?alpha_on ?tauM' //.
    rewrite cfdotBr cfdotZr rmorph_nat cfdotC !cfdotBl !cfdotZl !o_mu2_zeta.
    rewrite cfnorm_irr cfdotBr -{1}[mu_ k](Dade_Ind_chi cddM) -cfdot_Res_r.
    rewrite linearB linearZ cfdotBr !cfdotZr /= -!(Dade_chiE cddM) !cfdot_irr.
    rewrite !(inj_eq (Dade_irr_inj cddM)) 2![_ == _](negPf _) //.
    rewrite cfdot_suml big1 => [|j1 _]; last exact: o_mu2_zeta.
    by rewrite mulr1 !mulr0 -mulrN opprB !subr0 rmorph0 add0r.
  have <-: '[al_ij^\tau] * '[(mu_ k)^\tau1] = (2%:R + n ^+ 2) * w1%:R.
    by rewrite Itau1 ?mem_zchar ?Smu_ // (cfdot_mu cddM) eqxx mul1n nm_alij. 
  rewrite -Cint_normK ?cfCauchySchwarz // Cint_cfdot_vchar //.
  by rewrite Ztau1 ?mem_zchar ?Smu_.
Import ssrint.
have{ub_da2} a0 : a = 0.
  apply: contraTeq (d_gt1) => /(sqr_Cint_ge1 Za) a2_ge1.
  suffices: n == 0.
    rewrite mulf_eq0 invr_eq0 orbC -implyNb neq0CG /= subr_eq0 => /eqP Dd.
    by rewrite -ltC_nat -(normr_nat _ d) Dd normr_sign ltrr.
  suffices: n ^+ 2 < n + 1.
    have d_odd: odd d.
      apply: dvdn_odd (mFT_odd M); rewrite -dvdC_nat !nCdivE -(mu1 0 j) //.
      exact: integral_char.dvd_irr1_cardG.
    have: (2%:R %| n * w1%:R)%C.
      rewrite divfK ?neq0CG // -signrN signrE addrA -(natrD _ d 1).
      by rewrite rpredB ?(dvdC_nat 2) // dvdn2 ?odd_double // odd_add d_odd.
    rewrite -(truncCK Nn) -mulrSr -natrM -natrX ltC_nat (dvdC_nat 2) pnatr_eq0.
    rewrite dvdn2 odd_mul mFT_odd; case: (truncC n) => [|[|n1]] // _.
    by rewrite ltnS leqNgt (ltn_exp2l 1).
  apply: ltr_le_trans (_ : n * - delta + 1 <= _); last first.
    have ->: n + 1 = n * `|- delta| + 1 by rewrite normrN normr_sign mulr1.
    rewrite ler_add2r ler_wpmul2l ?Cnat_ge0 ?real_ler_norm //.
    by rewrite rpredN ?rpred_sign.
  rewrite -(ltr_pmul2r (ltC_nat 0 2)) mulrDl mul1r -[rhs in rhs + _]mulrA.
  apply: ler_lt_trans (_ : n ^+ 2 * (w1%:R - 1) < _).
    have: odd w1 && (1 < w1)%N by rewrite mFT_odd cardG_gt1.
    case: (w1) => [|[|[|m]]] _ //; rewrite -(@natrB _ _ 1) //=.
    by rewrite ler_wpmul2l ?Cnat_ge0 ?rpredX // leC_nat.
  rewrite -(ltr_pmul2l (gt0CG W1)) -/w1 2!mulrBr mulr1 mulrCA -exprMn.
  rewrite mulrDr ltr_subl_addl addrCA -mulrDr mulrCA mulrA -ltr_subl_addl.
  rewrite -mulrBr mulNr opprK divfK ?neq0CG // mulr_natr addrA subrK -subr_sqr.
  rewrite sqrr_sign mulrC [_ + 2%:R]addrC (ltr_le_trans _ ub_da2) //.
  apply: ltr_le_trans (ler_wpmul2l (ler0n _ _) a2_ge1).
  by rewrite mulr1 ltr_subl_addl -mulrS -natrX ltC_nat.
pose X := al_ij^\tau + n *: zeta^\tau1.
have oXzeta: '[X, zeta^\tau1] = 0.
  by rewrite cfdotDl cfdotZl Itau1 ?mem_zchar // cfnorm_irr mulr1.
have nmX: '[X] = 2%:R.
  apply: (addIr (n ^+ 2)); rewrite -nm_alij (canRL (addrK _) (erefl X)).
  rewrite cfnormBd ?cfnormZ ?cfdotZr ?oXzeta ?mulr0 // ?ger0_norm ?Cnat_ge0 //.
  by rewrite Itau1 ?mem_zchar // cfnorm_irr mulr1.
pose psi := X - delta *: (w_sig i j - w_sig i 0).
suffices: psi = 0.
  by rewrite -[psi]addrA => /(canRL (addrK _))->; rewrite add0r opprB.
have psiV0 y: y \in V -> psi y = 0.
  move=> Vy; rewrite !cfunE !(@cyclicTIsigma_restrict _ _ _ _ _ cddM) //.
  rewrite addrAC Dade_id ?(FTtypeP_supp0_def _ MtypeP) //; last first.
    by rewrite setUC inE (subsetP (sub_class_support _ _)).
  have notM'y: y \notin M'.
    by have:= subsetP (Ptype_TIset_disjoint cddM) y Vy; rewrite inE.
  have Wy: y \in W :\: W2 by move: Vy; rewrite !inE => /andP[/norP[_ ->]].
  have [/(_ _ _ y Wy) mu2y _] := Dade_mu2_restrict cddM.
  rewrite 2!cfunE mu2y Ddelta // !cfunE mu2y (Dade_delta0 cddM) scale1r.
  rewrite -mulrBr -addrA addrACA subrr (cfun_on0 (seqInd_on _ Szeta)) // mulr0.
  have [e /mem_subseq Re ->]:
    exists2 e, subseq e (rmR zeta) & zeta^\tau1 = \sum_(xi <- e) xi.
  - apply: (coherent_sum_subseq scohM) => //.
      have [ZItau1 _] := cohS; apply: sub_iso_to ZItau1 => //.
      by apply: zchar_subset; apply/allP; rewrite /= Szeta cfAut_seqInd.
    by rewrite Dtau1 ?seqInd_sub_aut_zchar.
  rewrite oppr0 !add0r sum_cfunE big1_seq ?mulr0 // => xi /Re Rxi.
  rewrite (@cyclicTIsigma_orthogonal _ _ _ _ _ cddM) // => ij1.
  apply: (orthoPr (FTtypeP_base_ortho maxM MtypeP _ (mem_irr _)) _ Rxi).
  by rewrite inE /= mem_irr (group_inj (FTcore_eq_der1 _ _)) ?Szeta.
set dsw := w_sig i j - _ in psi psiV0 *.
pose dmu := delta *: X; set phi := delta *: psi.
have Zmu: dmu \in 'Z[irr G].
  by rewrite rpredZsign rpredD ?rpredZ_Cnat // Ztau1 ?mem_zchar.
have Zsw: dsw \in 'Z[irr G].
  by have [_ Zsig] := cyclicTIisometry cddM; rewrite rpredB ?Zsig ?irr_vchar.
have n2mu: '[dmu] = 2%:R by rewrite cfnorm_sign nmX.
have n2sw: '[dsw] = 2%:R.
  by rewrite cfnormBd !(cfdot_sigma cddM) ?eqxx ?(negPf nz_j).
have [oImu _ Dmu] := dirr_small_norm (zcharW Zmu) n2mu isT.
have{Zsw} [oIsw _ Dsw] := dirr_small_norm Zsw n2sw isT.
set Imu := dirr_constt _ in oImu Dmu; set Isw := dirr_constt _ in oIsw Dsw.
have mu'sw_lt0 di: di \in Isw :\: Imu -> '[phi, dchi di] < 0.
  case/setDP=> sw_di mu'di; rewrite /phi scalerBr signrZK cfdotBl subr_lt0.
  move: sw_di; rewrite dirr_consttE; apply: ler_lt_trans.
  rewrite real_lerNgt -?dirr_consttE ?real0 ?Creal_Cint //.
  by rewrite Cint_cfdot_vchar ?(zcharW Zmu) ?dchi_vchar.
suffices /eqP eqI_sw_mu: Isw == Imu.
  by rewrite /psi Dsw eqI_sw_mu -Dmu signrZK subrr.
rewrite eqEcard oImu oIsw andbT -setD_eq0; apply/set0Pn=> [[dj1 mu'dj1]].
have [[sw_dj1 _] phi_j1_lt0] := (setDP mu'dj1, mu'sw_lt0 _ mu'dj1).
have NCtrB := leq_trans (cyclicTI_NC_sub W W1 W2 (_ : 'CF(G)) _) (leq_add _ _).
set NC := cyclicTI_NC _ _ _ in NCtrB.
have NCb k: (NC (dchi k) <= 1)%N by rewrite (cyclicTI_NC_dirr cddM) ?dirr_dchi.
have Wi_gt2 (Wi : {group gT}): Wi :!=: 1%g -> (#|Wi| > 2)%N.
  rewrite -cardG_gt1 -[#|Wi|]odd_double_half mFT_odd !ltnS.
  by rewrite (ltn_double 0) (leq_double 1).
have ntW2: W2 :!=: 1%g by rewrite -cardG_gt1.
have ltNCphi: (NC phi < 2 * minn #|W1| #|W2|)%N.
  suffices NCphi4: (NC phi <= 1 + 1 + (1 + 1))%N.
    rewrite (leq_ltn_trans NCphi4) // !addnn -mul2n ltn_pmul2l // leq_min.
    by rewrite !Wi_gt2.
  rewrite /phi scalerBr signrZK -/dmu.
  have{n2mu} [n2mu _ ->] := dirr_small_norm Zmu n2mu isT.
  rewrite -big_filter filter_index_enum (big_nth (dirr1 _)) -cardE n2mu.
  move: (nth _ _) => b; rewrite big_nat_recr -[dchi _]opprK -dchi_ndirrE.
  rewrite big_ltn ?big_geq //= addr0.
  by rewrite !NCtrB ?NCb // /NC (cyclicTI_NC_sigma cddM).
pose swId := dirr_dIirr (fun sj => (-1) ^+ (sj.1 : bool) *: sigma (w_ i sj.2)).
have swIdE s l: dchi (swId (s, l)) = (-1) ^+ s *: sigma (w_ i l).
  by apply: dirr_dIirrE => sj; rewrite rpredZsign (dirr_sigma cddM).
have dot_dj1: '[dsw, dchi dj1] = 1.
  rewrite Dsw cfdot_suml (big_setD1 dj1) //= cfnorm_dchi big1 ?addr0 //.
  move=> dj2 /setD1P[/negPf j1'2 /dirr_constt_oppl]; rewrite cfdot_dchi j1'2.
  by case: eqP => [-> /negP[] | _ _]; rewrite ?subrr ?ndirrK.
have dot_dj2: 0 < '[dsw, dsw - dchi dj1].
  by rewrite cfdotBr dot_dj1 n2sw addrK ltr01.
have{dot_dj1 dot_dj2} [s [j1 [j2 Dj1 sw_j2]]]:
  exists s, exists j1, exists2 j2, swId (s, j1) = dj1 & swId (~~ s, j2) \in Isw.
- move/cfdot_add_dirr_eq1: dot_dj1.
  rewrite dirr_dchi rpredN !(dirr_sigma cddM) //.
  case=> // Ddj1; [exists false, j, 0 | exists true, 0, j]; try apply: dirr_inj;
    rewrite ?dirr_consttE swIdE scaler_sign //=.
  + by rewrite addrC Ddj1 addKr in dot_dj2.
  by rewrite Ddj1 addrK in dot_dj2.
rewrite -Dj1 swIdE cfdotZr rmorph_sign in phi_j1_lt0.
have phi_j1_neq0: '[phi, sigma (w_ i j1)] != 0.
  by rewrite -(can_eq (signrMK s)) mulr0 ltr_eqF.
set dj2 := swId _ in sw_j2; have NCj2'_le1 (dI : {set _}):
  dj2 \in dI -> #|dI| = 2%N -> (NC (\sum_(dk in dI :\ dj2) dchi dk)%R <= 1)%N.
- rewrite (cardsD1 dj2) => -> /eqP/cards1P[dk ->].
  by rewrite big_set1 NCb.
have V'phi y: y \in V -> phi y = 0 by move=> Vy; rewrite cfunE psiV0 ?mulr0.
suffices /mu'sw_lt0/ltr_geF/idP[]: dj2 \in Isw :\: Imu.
  rewrite swIdE cfdotZr signrN rmorphN mulNr oppr_ge0 rmorph_sign.  
  have := cyclicTI_NC_split V'phi ltNCphi phi_j1_neq0.
  by case/(_ cddM)=> ->; rewrite mulrCA nmulr_lle0 ?ler0n.
have cycW_G : cyclicTIhypothesis G W W1 W2 := cddM.
have: (1 + 1 < NC phi)%N.
  apply (@leq_trans (minn #|W1| #|W2|)); first by rewrite leq_min ?Wi_gt2.
  apply: cyclicTI_NC_minn => //; rewrite ltNCphi /NC /cyclicTI_NC.
  by rewrite (cardsD1 (i, j1)) inE /= phi_j1_neq0.
rewrite inE sw_j2 andbT ltnNge; apply: contra => mu_j2.
rewrite /phi scalerBr signrZK -/dmu Dsw (big_setD1 dj2) //=.
rewrite Dmu (big_setD1 dj2) //=.
by rewrite addrAC opprD addNKr addrC NCtrB ?NCj2'_le1.
Qed.

(* This is the first part of Peterfalvi (10.6)(a). *)
Let tau1mu j : j != 0 -> (mu_ j)^\tau1 = delta *: \sum_i w_sig i j.
Proof.
move=> nz_j; have [[Itau1 _] _] := cohS.
have Smu_j: mu_ j \in calS.
  rewrite /mu_ -(Dade_Ind_chi cddM) mem_seqInd ?normal1 // !inE sub1G andbT.
  rewrite subGcfker -irr_eq1 -(Dade_chi0 cddM) (inj_eq irr_inj).
  by rewrite (inj_eq (Dade_irr_inj cddM)).    
have wsig_mu i: '[delta *: (w_sig i j - w_sig i 0), (mu_ j)^\tau1] = 1.
  have Szeta_s: zeta^*%CF \in calS by rewrite cfAut_seqInd.
  have o_zeta_s_w k: '[w_sig i k, d%:R *: zeta^*^\tau1] = 0.
    have [e /mem_subseq Re ->]:
      exists2 e, subseq e (rmR zeta^*) & zeta^*^\tau1 = \sum_(xi <- e) xi.
    - apply: (coherent_sum_subseq scohM) => //.
        have [ZItau1 _] := cohS; apply: sub_iso_to ZItau1 => //.
        by apply: zchar_subset; apply/allP; rewrite /= Szeta_s cfAut_seqInd.
      by rewrite Dtau1 ?seqInd_sub_aut_zchar.
    rewrite cfdotZr cfdotC cfdot_suml big1_seq ?rmorph0 ?mulr0 // => xi /Re Rxi.
    apply: (orthoPr (FTtypeP_base_ortho maxM MtypeP _ (mem_irr _)) _ Rxi).
    rewrite inE /= (group_inj (FTcore_eq_der1 _ _)) // Szeta_s.
    by rewrite -aut_IirrE mem_irr.
  rewrite -[_^\tau1](subrK (d%:R *: zeta^*^\tau1)) cfdotDr addrC.
  rewrite cfdotZl cfdotBl !{}o_zeta_s_w subrr mulr0 add0r.
  rewrite -(canLR (subrK _) (tau_alpha i nz_j)) cfdotDl addrC cfdotZl.
  rewrite cfdotBr !cfdotZr !Itau1 ?mem_zchar //.
  rewrite (seqInd_conjC_ortho _ _ _ Szeta) ?mFT_odd // mulr0 subr0.
  rewrite cfdotC cfdot_suml big1 // rmorph0 mulr0 add0r.
  rewrite -raddfZnat -(raddfB tau1); set psi := _ - _.
  have Zpsi: psi \in 'Z[calS, M'^#].
    have [mu1 _ _ _] := FTtype345_invariants.
    rewrite /psi -[d%:R](mulKf (neq0CiG M M')) mulrC -(mu1 0 j nz_j).
    rewrite -(cfResE _ sM'M) // -(Dade_chiE cddM) -cfInd1 //.
    rewrite (Dade_Ind_chi cddM) (seqInd_sub_lin_vchar _ Szeta_s) //.
    by rewrite cfunE zeta1w1 rmorph_nat -(index_sdprod defM).
  rewrite Dtau1 // Dade_isometry ?alpha_on ?tauM' //.
  rewrite !(cfdotBl, cfdotZl, cfdotBr, cfdotZr).
  rewrite (seqInd_conjC_ortho _ _ _ Szeta) ?mFT_odd // mulr0 subr0.
  rewrite -{1 2}[mu_ j](Dade_Ind_chi cddM) -!cfdot_Res_l -!(Dade_chiE cddM).
  rewrite cfnorm_irr cfdot_irr (inj_eq (Dade_irr_inj cddM)) eq_sym (negPf nz_j).
  rewrite -[mu2_ i j]cfConjCK  -[mu2_ i 0]cfConjCK !cfdot_conjC.
  rewrite -!(Dade_mu2_aut cddM) !o_mu2_zeta rmorph0 !(mulr0, subr0).
  by rewrite cfdotC cfdot_suml big1 // rmorph0 mulr0 subr0.
have S_k: has (mem (irr M)) calS /\ mu_ j \in calS.
  by split=> //; apply/hasP; exists zeta; rewrite //= mem_irr.
have Dmu := def_Ptype_coherent_mu _ S_k.
move/Dmu: cddM => {Dmu}Dmu; move/Dmu: cohS => {Dmu}Dmu.
case: Dmu; last 2 [by have [_ ->] := FTtype345_invariants].
  rewrite seqInd_uniq (group_inj (FTcore_eq_der1 _ _)) //.
  by rewrite seqInd_notReal ?mFT_odd //; split=> //; apply: cfAut_seqInd.
rewrite -!/(mu_ _); have [_ -> // _ _] := FTtype345_invariants.
case=> Dmu _; have /eqP/idPn[] := wsig_mu 0.
rewrite eq_sym Dmu cfdotZl cfdotZr cfdot_sumr big1 ?mulr0 ?oner_eq0 // => i _.
rewrite cfdotBl !(cfdot_sigma cddM) !(eq_sym 0).
rewrite -!irr_eq1 -(inj_eq irr_inj) -{1}[j]conjC_IirrK aut_IirrE.
by rewrite odd_eq_conj_irr1 ?mFT_odd // aut_IirrE subrr.
Qed.

(* This is the second part of Peterfalvi (10.6)(a). *)
Let tau1mu0 : (mu_ 0 - zeta)^\tau = \sum_i w_sig i 0 - zeta^\tau1.
Proof.
have [[cycW1 _ _ _] _ _ [cycW2 ntW2 _ _ _] _] := MtypeP.
have [j nz_j] := has_nonprincipal_irr ntW2.
have sum_al: \sum_i alpha_ i j = mu_ j - d%:R *: zeta - delta *: (mu_ 0 - zeta).
  rewrite !sumrB sumr_const -scaler_sumr card_Iirr_abelian ?cyclic_abelian //.
  rewrite -scaler_nat scalerA mulrC divfK ?neq0CG // -!addrA -!opprD.
  by rewrite scalerBl scalerBr addrCA.
rewrite -(signrZK _ _ : delta *: _ =  _ - zeta) -/delta.
rewrite (canRL (addKr _) (canLR (subrK _) sum_al)).
have Smu_j: mu_ j \in calS.
  rewrite /mu_ -(Dade_Ind_chi cddM) mem_seqInd ?normal1 // !inE sub1G andbT.
  rewrite subGcfker -irr_eq1 -(Dade_chi0 cddM) (inj_eq irr_inj).
  by rewrite (inj_eq (Dade_irr_inj cddM)).    
have Zpsi: mu_ j - d%:R *: zeta \in 'Z[calS, M'^#].
  have [mu1 _ _ _] := FTtype345_invariants.
  rewrite -[d%:R](mulKf (neq0CiG M M')) mulrC -(mu1 0 j nz_j).
  rewrite -(cfResE _ sM'M) // -(Dade_chiE cddM) -cfInd1 //.
  rewrite (Dade_Ind_chi cddM) (seqInd_sub_lin_vchar _ Szeta) //.
  by rewrite -(index_sdprod defM).
rewrite linearZ linearD linearN linear_sum /= -(Dtau1 Zpsi).
rewrite raddfB raddfZnat tau1mu // scalerDr scalerBr signrZK addrCA.
rewrite (eq_bigr _ (fun i _ => tau_alpha i nz_j)) sumrB sumr_const opprB.
rewrite -scaler_sumr scalerDr scalerN signrZK sumrB.
rewrite card_Iirr_abelian ?cyclic_abelian // -/w1 -scaler_nat !scalerA.
rewrite mulrAC -mulrA divfK ?neq0CG // mulrBr scalerBl.
rewrite addrA addrC -!addrA addrCA addKr addrCA -scalerA signrZK.
by rewrite addrC opprD opprK addNKr.
Qed.

(* This is Peterfalvi (10.6)(b). *)
Let zeta_tau1_coprime g :
  g \notin 'A~(M) -> coprime #[g] w1 -> `|zeta^\tau1 g| >= 1.
Proof.
Admitted.

End NonCoherence.

End OneMaximal.

End Ten.
