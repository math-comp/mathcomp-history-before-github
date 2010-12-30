(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div path fintype.
Require Import bigop finset prime fingroup morphism perm automorphism quotient.
Require Import action gproduct gfunctor pgroup cyclic center commutator.
Require Import gseries nilpotent sylow abelian maximal hall frobenius.
Require Import BGsection1 BGsection3 BGsection4 BGsection5 BGsection6.
Require Import BGsection7 BGsection9 BGsection10 BGsection12 BGsection13.
Require Import BGsection14.

(******************************************************************************)
(*   This file covers B & G, section 15; it fills in the picture of maximal   *)
(* subgroups that was sketched out in section14, providing an intrinsic       *)
(* characterization of M`_\sigma and establishing the TI property for the     *)
(* "kernels" of maximal groups. We introduce only one new definition:         *)
(*    M`_\F == the (direct) product of all the normal Sylow subgroups of M;   *)
(*             equivalently, the largest normal nilpotent Hall subgroup of M  *)
(*             We will refer to M`_\F as the Fitting core or F-core of M.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Definitions.

Variables (gT : finGroupType) (M : {set gT}).

Definition Fitting_core :=
  <<\bigcup_(P : {group gT} | Sylow M P && (P <| M)) P>>.
Canonical Structure Fitting_core_group := [group of Fitting_core].

End Definitions.

Notation "M `_ \F" := (Fitting_core M)
  (at level 3, format "M `_ \F") : group_scope.
Notation "M `_ \F" := (Fitting_core_group M) : subgroup_scope.

Section FittingCore.

Variable (gT : finGroupType) (M : {group gT}).
Implicit Types H P : {group gT}.
Implicit Type p : nat.

Lemma Fcore_normal : M`_\F <| M.
Proof.
rewrite -[M`_\F]bigprodGE.
apply big_prop => [|P Q nsP nsG|P]; [exact: normal1 | | by case/andP].
by rewrite /normal normsY ?normal_norm // join_subG ?normal_sub.
Qed.
Hint Resolve Fcore_normal.

Lemma Fcore_sub : M`_\F \subset M.
Proof. by case/andP: Fcore_normal. Qed.

Lemma Fcore_sub_Fitting : M`_\F \subset 'F(M).
Proof.
rewrite gen_subG; apply/bigcupsP=> P; case/andP; case/SylowP=> p _.
by case/and3P=> _ pP _ nsP; rewrite Fitting_max // (pgroup_nil pP).
Qed.

Lemma Fcore_nil : nilpotent M`_\F.
Proof. exact: nilpotentS Fcore_sub_Fitting (Fitting_nil M). Qed.

Lemma Fcore_max : forall pi H,
  pi.-Hall(M) H -> H <| M -> nilpotent H -> H \subset M`_\F.
Proof.
move=> pi H hallH nsHM nilH; have [sHM pi_H _] := and3P hallH.
rewrite -(nilpotent_Fitting nilH) FittingEgen genS //.
apply/bigcupsP=> [[p /= _] piHp]; rewrite (bigcup_max 'O_p(H)%G) //.
have sylHp := nilpotent_pcore_Hall p nilH.
have sylHp_M := subHall_Sylow hallH (pnatPpi pi_H piHp) sylHp.
by rewrite (p_Sylow sylHp_M) (char_normal_trans (pcore_char _ _)).
Qed.

Lemma Fcore_dprod : \big[dprod/1]_(P | Sylow M (gval P) && (P <| M)) P = M`_\F.
Proof.
rewrite -[M`_\F]bigprodGE; apply/eqP; apply/bigdprodYP=> P; case/andP.
case/SylowP=> p p_pr sylP nsPM; have defP := normal_Hall_pcore sylP nsPM.
have [_ _ cFpFp' tiFpFp'] := dprodP (nilpotent_pcoreC p (Fitting_nil M)).
move/dprodYP: (dprodEY cFpFp' tiFpFp'); rewrite /= p_core_Fitting defP.
apply: subset_trans; rewrite bigprodGE gen_subG.
apply/bigcupsP=> Q; do 2![case/andP]; case/SylowP=> q _ sylQ nsQM neqQP.
have defQ := normal_Hall_pcore sylQ nsQM; rewrite -defQ -p_core_Fitting.
apply: sub_pcore => q'; move/eqnP->; apply: contraNneq neqQP => eq_qp.
by rewrite -val_eqE /= -defP -defQ eq_qp.
Qed.

Lemma Fcore_pcore_Sylow : forall p, p \in \pi(M`_\F) -> p.-Sylow(M) 'O_p(M).
Proof.
move=> p /=; rewrite -(bigdprod_card Fcore_dprod) mem_primes.
case/and3P=> p_pr _; have ?: ~ p %| 1 by rewrite gtnNdvd ?prime_gt1.
apply big_prop=> // [p1 p2 IH1 IH2|P].
  rewrite euclid //; case/orP; [exact: IH1 | exact: IH2].
case/andP; case/SylowP=> q q_pr sylP nsPM p_dv_P; have qP := pHall_pgroup sylP.
by rewrite (eqnP (pgroupP qP p p_pr p_dv_P)) (normal_Hall_pcore sylP).
Qed.

Lemma p_core_Fcore : forall p, p \in \pi(M`_\F) -> 'O_p(M`_\F) = 'O_p(M).
Proof.
move=> p piMFp /=; rewrite -(pcore_setI_normal p Fcore_normal).
apply/setIidPl; rewrite sub_gen // (bigcup_max 'O_p(M)%G) //= pcore_normal.
by rewrite (p_Sylow (Fcore_pcore_Sylow piMFp)).
Qed.

Lemma Fcore_Hall : \pi(M`_\F).-Hall(M) M`_\F.
Proof.
rewrite Hall_pi // /Hall Fcore_sub coprime_pi' ?cardG_gt0 //=.
apply/pnatP=> // p p_pr; apply: contraL => /= piMFp; rewrite -p'natE //.
rewrite -partn_eq1 // -(eqn_pmul2l (part_gt0 p #|M`_\F|)) muln1.
rewrite -partn_mul ?cardG_gt0 // LaGrange ?Fcore_sub //.
rewrite -(card_Hall (nilpotent_pcore_Hall p Fcore_nil)) /=.
by rewrite p_core_Fcore // (card_Hall (Fcore_pcore_Sylow piMFp)).
Qed.

Lemma pcore_Fcore : forall pi,
  {subset pi <= \pi(M`_\F)} -> 'O_pi(M`_\F) = 'O_pi(M).
Proof.
move=> pi s_pi_MF; rewrite -(pcore_setI_normal pi Fcore_normal); apply/setIidPl.
rewrite (sub_normal_Hall Fcore_Hall) ?pcore_sub //.
exact: sub_pgroup s_pi_MF (pcore_pgroup pi M).
Qed.

Lemma Fcore_pcore_Hall : forall pi,
  {subset pi <= \pi(M`_\F)} -> pi.-Hall(M) 'O_pi(M).
Proof.
move=> pi s_pi_MF; apply: (subHall_Hall Fcore_Hall s_pi_MF).
by rewrite /= -pcore_Fcore // (nilpotent_pcore_Hall pi Fcore_nil).
Qed.

End FittingCore.

Lemma Fcore_continuity : cont Fitting_core.
Proof.
move=> gT rT G f.
apply: (Fcore_max (morphim_pHall f (Fcore_sub G) (Fcore_Hall G))).
  by rewrite morphim_normal ?Fcore_normal.
by rewrite morphim_nil ?Fcore_nil.
Qed.

Lemma Fcore_hereditary : hereditary Fitting_core.
Proof.
move=> gT H G sHG; have nsGF_G := Fcore_normal G.
apply: Fcore_max (setI_normal_Hall nsGF_G (Fcore_Hall G) sHG) _ _.
  by rewrite /= setIC (normalGI sHG) //.
exact: nilpotentS (subsetIl _ _) (Fcore_nil G).
Qed.

Canonical Structure bgFunc_Fcore := [bgFunc by Fcore_sub & Fcore_continuity].

Canonical Structure gFunc_Fcore := GFunc Fcore_continuity.

Canonical Structure hgFunc_Fcore := HGFunc Fcore_hereditary.

Section MoreFittingCore.

Variables (gT rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).
Implicit Type M H : {group gT}.

Lemma Fcore_char : forall M, M`_\F \char M. Proof. exact: bgFunc_char. Qed.

Lemma FcoreJ : forall M x, (M :^ x)`_\F = M`_\F :^ x.
Proof.
move=> M x; rewrite -{1}(setTI M) -morphim_conj.
by rewrite -bgFunc_ascont ?injm_conj ?subsetT // morphim_conj setTI.
Qed.

Lemma morphim_Fcore : forall M, f @* M`_\F \subset (f @* M)`_\F.
Proof. move=> M; exact: hgFunc_morphim. Qed.

Lemma injm_Fcore : forall M,
  'injm f -> M \subset D -> f @* M`_\F = (f @* M)`_\F.
Proof. by move=> M injf sMD; rewrite bgFunc_ascont. Qed.

Lemma isom_Fcore : forall M (R : {group rT}),
  isom M R f -> M \subset D -> isom M`_\F R`_\F f.
Proof. by move=> M R isoMR sMD; exact: bgFunc_isom. Qed.

Lemma isog_Fcore : forall M (R : {group rT}), M \isog R -> M`_\F \isog R`_\F.
Proof. by move=> M R isoMR; exact: bgFunc_isog. Qed.

End MoreFittingCore.

Section Section15.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types p q q_star r : nat.
Implicit Types x y z : gT.
Implicit Types A E H K L M Mstar N P Q Qstar R S T U V W X Y Z : {group gT}.

Lemma Fcore_sub_Msigma : forall M, M \in 'M -> M`_\F \subset M`_\sigma.
Proof.
move=> M maxM; rewrite gen_subG; apply/bigcupsP=> P; case/andP.
case/SylowP=> p _ sylP nsPM; have [sPM pP _] := and3P sylP.
have [-> | ntP] := eqsVneq P 1; first exact: sub1G.
rewrite (sub_Hall_pcore (Msigma_Hall maxM)) // (pi_pgroup pP) //.
by apply/exists_inP; exists P; rewrite ?(mmax_normal maxM).
Qed.

Lemma Fcore_eq_Msigma : forall M,
  M \in 'M -> reflect (M`_\F = M`_\sigma) (nilpotent M`_\sigma).
Proof.
move=> M maxM; apply: (iffP idP) => [nilMs | <-]; last exact: Fcore_nil.
apply/eqP; rewrite eqEsubset Fcore_sub_Msigma //.
by rewrite (Fcore_max (Msigma_Hall maxM)) ?pcore_normal.
Qed.

End Section15.


