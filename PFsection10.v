(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8 PFsection9.

(******************************************************************************)
(* This file covers Peterfalvi, Section 10: Maximal subgroups of Types III,   *)
(* IV and V. Defined here:                                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.

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

(*
Local Notation sigma i j := (@cyclicTIsigma _ [set: _] W W1 W2 i j).
Local Notation w_ i j := (@cyclicTIirr _ [set: _] W W1 W2 i j).
Local Notation mu2_ i j := (@Dade_mu2 _ M W W1 W2 i j).
Local Notation mu_ j := (@Dade_mu _ M W W1 W2 j).
Local Notation delta_ j := (@Dade_delta _ M W W1 W2 j).
*)

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
Let w2_gt0 : w2 > 0. Proof. exact: prime_gt0. Qed.
Let w2_gt1 : w2 > 1. Proof. exact: prime_gt1. Qed.

Definition FTtype345_mu_degree := truncC (mu2_ 0 (inord 1) 1%g).
Definition FTtype345_mu_sign := delta_ (inord 1).
Local Notation d := FTtype345_mu_degree.
Local Notation delta := FTtype345_mu_sign.
Definition FTtype345_reduced_mu_degree := (d%:R - delta) / w1%:R.
Local Notation n := FTtype345_reduced_mu_degree.

Import ssrnum Num.Theory.

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
  pose cTIcc := cyclicTI_Dade cddM; pose defW := cyclicTIhyp_W1xW2 cTIcc.
  have w_Er k: w_ 0 k = cfDprodr defW 'chi_k.
    by rewrite [w_ 0 k](cTIirrE cTIcc) dprod_IirrE irr0 cfDprod_cfun1l.
  have oi0j1: #[w_ 0 j1]%CF = #['chi_j1]%CF.
    apply/eqP; rewrite w_Er eqn_dvd; apply/andP; split.
      apply/dvdn_cforderP=> _ /(mem_dprod defW)[x [y [W1x W2y -> _]]].
      by rewrite cfDprodEr //; apply/dvdn_cforderP.
    apply/dvdn_cforderP=> y W2y; rewrite -(cfDprodEr defW _ (group1 W1)) //.
    by apply/dvdn_cforderP; rewrite //= -(dprodW defW) mem_mulg.
  move/gen_lW2=> gen_j; have gen_j1 := (_ =P <[_]>) (gen_lW2 _ nz_j1).
  rewrite gen_j1 in gen_j; have /cycleP[m Dj] := cycle_generator gen_j.
  rewrite Dj generator_coprime o_cF -cF'K -oi0j1 coprime_sym in gen_j.
  have [[u Dj1u] _] := cyclicTI_aut_exists cTIcc gen_j.
  do [rewrite -['chi__]/(w_ _ _); set sig_mu := cyclicTIsigma _ _ _ _] in Dj1u.
  rewrite {1}w_Er -rmorphX cF'K -cF_X -Dj -cF'K /= -w_Er in Dj1u.
  rewrite truncCK ?Cnat_irr1 // -/j1.
  have: delta_ j *: mu2_ 0 j == cfAut u (delta_ j1 *: mu2_ 0 j1).
    by rewrite -!(Dade_mu2_sigma cddM) -/sig_mu -/cTIcc -/defW -Dj1u.
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
split=> // [i j /invj[<- _] | _ /invj[//] | ].
  by rewrite -!(@cfRes1 _ M' M) (Dade_chi_eq cddM).
have: (d%:R == delta %[mod w1])%C.
  by rewrite truncCK ?Cnat_irr1 ?(Dade_mu2_mod cddM).
rewrite /eqCmod unfold_in -/n (negPf (neq0CG W1)) CnatEint => ->.
rewrite divr_ge0 ?ler0n // [delta]signrE opprB addrA -natrD subr_ge0 ler1n.
by rewrite -(subnKC d_gt1).
Qed.

End OneMaximal.

End Ten.
