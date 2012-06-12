(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation mxabelem vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection15 BGsection16.
Require Import ssrnum ssrint algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4.
Require Import PFsection5 PFsection6 PFsection8 PFsection9.
Require Import PFsection11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section PFTwelve.

(* Hypothesis 12.1 *)
Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).

Section Twelve2.

Variable L : {group gT}.

Hypothesis maxL : L \in 'M.

(* bool equal is better in order to provide a quicker access to the reflection 
lemma FTtypeP *)
Hypothesis Ltype : FTtype L == 1%N.

(* in order to use H both as a group and a set *)
(* notation can be overloaded this way but not with a simple notation *)
Local Notation "'H'" := (gval L)`_\F (at level 0) : group_scope.
Local Notation "'H'" := (gval L)`_\F%G : Group_scope.

(* Warning : we need gval for the set version, because otherwise,
because L is a group and when we enter H, if Coq needs to insert the *)
(* coercion around L once the notation have been interpreted, then the *)
(* notation will no more be displayed. Test this with Check H'. *)

(* Prefer the (convertible) derived group version to the commutator expression,
since it's most often used as such in the proofs *)
Local Notation H' := H^`(1).

(* This is wrong : we define here 
{\theta \in Irr (L) | H \in ker \theta and 1%g is not included in ker \theta 
otherwise said the empty set.
Local Notation calS := (Iirr_kerD L 1%g H).*)

(* use Let instead of Local Notation to avoid unused occurrences of H *)
Let calS := seqIndD H L H 1%G.

(* there is hidden occurrences of L here so let's use let *)
Let tau := FT_Dade0 maxL.

(* Remark : if the objet you're defining is equipped with some *)
(* canonical structure, the CS can be infered under a let but the definition *)
(* is expanded and you'll have to fold it back by hand after inference *)
(* took place. A local notation might be a better option *)

Let S_ (chi : 'CF(L)) := [set i in irr_constt chi].

Set Printing Width 35.

(* theorem 5.7 expects the independance statement to be expressed as *)
(* such *)
Lemma PF_12_2a chi : chi \in calS ->
  [/\ chi = \sum_(i in S_ chi) 'chi_i,
      constant [seq 'chi_i 1%g | i in S_ chi] &
      {in S_ chi, forall i, 'chi_i \in 'CF(L, 1%g |: 'A(L))}].
Proof.
case/seqIndC1P=> t kert Dchi.
have nHL : H <| L by exact: gFnormal.
pose T := 'I_L['chi_t]%g.
have sTL : T \subset L by exact: inertia_sub.
have sHT : H \subset T by apply: sub_inertia; exact: gFsub.
have sHL : H \subset L by apply: normal_sub.
have copHIchi : coprime #|H| #|T : H|.
  suff : (\pi(H)).-Hall(T) H by case/pHall_Hall /andP.
  by apply: pHall_subl _ (Fcore_Hall L).
have [U [Utype _]] := FTtypeP _ maxL Ltype.
have [[_ _ sdHU] [U1 inertU1] _] := Utype.
have defT: H ><| 'I_U['chi_t] = T.
  have := sdprod_modl sdHU sHT.
  rewrite {1}(setIidPr sTL).
    (* should be a lemme in inertia: *)
  have /sdprod_context [_ sUL _ _ _]:= sdHU.
  by rewrite /= !['I__[_]]setIdE setIA (setIidPl sUL).
have abTbar : abelian (T / H).
  have [_ _ /(_ _ _ inertU1 kert) sItU1] := (typeF_context Utype).
  have [nU1U abU1 _] := inertU1.
  rewrite /T; have /sdprodP [_ <- _ _] := defT.
  by rewrite quotientMidl quotient_abelian // (abelianS sItU1).
have Dchi_sum : chi = \sum_(i in S_ chi) 'chi_i.
  rewrite {1}Dchi.
  have /= [-> _] := induced_inertia_quo1 nHL abTbar copHIchi.
  rewrite -/T.
  have Dchi_irr := cfIirrE (cfInd_constt_inertia_irr nHL _).
  rewrite (reindex_onto (fun j => cfIirr ('Ind[L] 'chi_j)) 
     (fun j => inertia_Ind_inv t 'chi_j)) /=; last first.
    move=> j; rewrite inE Dchi constt_Ind_constt_Res => Sj; apply irr_inj.
    by rewrite Dchi_irr ?constt_inertia_Ind_inv ?inertia_Ind_invE.
  apply: eq_big => [j | j Sj]; last by rewrite Dchi_irr -?constt_Ind_constt_Res.
  rewrite [in X in _ = X]inE Dchi !constt_Ind_constt_Res; apply/idP/idP.
  - move=> irrj.
    rewrite {1}Dchi_irr // constt_Res_constt_inertia //=; apply/eqP.
    apply: single_constt_inertia => //.
      rewrite -Dchi_irr //= cfIirrE ?mem_irr // inertia_Ind_inv_constt //.
      by rewrite Dchi_irr // constt_Res_constt_inertia.
    by rewrite constt_inertia_Ind_inv // Dchi_irr // constt_Res_constt_inertia.
  - by case/andP => ht /eqP <-;  rewrite constt_inertia_Ind_inv.
have lichi : constant [seq 'chi_i 1%g | i in  S_ chi].
  have /= [_ [h_ Ichi1]] := induced_inertia_quo1 nHL abTbar copHIchi.
  pose c := #|L : T|%:R * 'chi_t 1%g.
  apply/(@all_pred1_constant _ c)/allP=> _ /mapP[psi Spsi ->] /=.
  move: Spsi; rewrite mem_enum inE Dchi => psi_irr; move: (psi_irr).
  rewrite constt_Ind_constt_Res; move/(inertia_Ind_invE nHL)<-; rewrite Ichi1 //. 
  by rewrite constt_Ind_constt_Res constt_inertia_Ind_inv -?constt_Ind_constt_Res.
Admitted.

Lemma tau_isometry  :
    {in 'Z[[seq 'chi_i | i in  \bigcup_(chi <- calS) S_ chi], L^#], 
      isometry tau, to 'Z[irr G]}.
Admitted.

End Twelve2.

End PFTwelve.


