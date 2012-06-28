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

(* Workaround for the absence of overloading for simple Notation: while H     *)
(* denotes a {group gT}, `H denotes its {set gT} projection.                  *)
Local Notation "` 'L'" := (gval L) (at level 0, only parsing) : group_scope.
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F (at level 0) : group_scope.

(* Warning : we need gval for the set version, because otherwise,
because L is a group and when we enter H, if Coq needs to insert the *)
(* coercion around L once the notation have been interpreted, then the *)
(* notation will no more be displayed. Test this with Check H'. *)

(* Prefer the (convertible) derived group version to the commutator expression,
since it's most often used as such in the proofs *)
Local Notation H' := H^`(1)%G.
Local Notation "` 'H''" := `H^`(1) (at level 0) : group_scope.

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

(* This is Peterfalvi (12.2a), first part *)
Lemma PF_12_2a chi : chi \in calS ->
  [/\ chi = \sum_(i in S_ chi) 'chi_i,
      constant [seq 'chi_i 1%g | i in S_ chi] &
      {in S_ chi, forall i, 'chi_i \in 'CF(L, 'A(L) :|: 1%G)}].
Proof.
case/seqIndC1P=> t kert Dchi.
have nHL : H <| L by exact: gFnormal.
pose T := 'I_L['chi_t]%g.
have sTL : T \subset L by exact: Inertia_sub.
have sHT : H \subset T by apply: sub_Inertia; exact: gFsub.
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
  rewrite {1}Dchi; have /= [-> _ _] := induced_inertia_quo1 nHL abTbar copHIchi.
  by rewrite Dchi (eq_bigl _ _ (in_set _)) (reindex_constt_inertia _ _ id).
have lichi : constant [seq 'chi_i 1%g | i in  S_ chi].
  have /= [_ _ Ichi1] := induced_inertia_quo1 nHL abTbar copHIchi.
  pose c := #|L : T|%:R * 'chi_t 1%g.
  apply/(@all_pred1_constant _ c)/allP=> _ /mapP[psi Spsi ->] /=.
  move: Spsi; rewrite mem_enum inE Dchi => psi_irr; move: (psi_irr).
  rewrite constt_Ind_constt_Res; move/(inertia_Ind_invE nHL)<-; rewrite Ichi1 //. 
  by rewrite constt_Ind_constt_Res constt_inertia_Ind_inv -?constt_Ind_constt_Res.
suff CF_S : {in S_ chi, forall i : Iirr L, 'chi_i \in 'CF(L, 'A(L) :|: 1%G )} by [].
  move=> j Schi_j /=; apply/cfun_onP => y nA1y.
  case: (boolP (y \in L)) => [Ly | ?]; last by rewrite cfun0.
  have CHy1 : 'C_H[y] = 1%g.
    move: nA1y; rewrite /FTsupport Ltype /= derg0 inE negb_or.
    rewrite /FTsupport1 /FTcore (eqP Ltype) /= in_set1; case/andP=> hy ny1.
    apply/trivgP; apply/subsetP=> z hz; rewrite in_set1.
    apply: contraLR hz => zn1; case: (boolP (z \in H)) => //= Hz; last first.
      by rewrite inE (negPf Hz).
    suff : y \notin 'C_L[z]^#.
      apply: contra; case/subcent1P=> _ cyz; rewrite in_setD1 ny1 /=.
      by apply/subcent1P; split => //; apply: commute_sym.
    apply: contra hy => hy; apply/bigcupP; exists z => //; rewrite inE in_set1.
    by rewrite zn1.
  suff nHkerS : ~~ (H \subset cfker 'chi_j).
    by apply: (not_in_ker_char0 _ _ nHkerS).
  move: Schi_j; rewrite inE Dchi.
  move/sub_cfker_constt_Ind_irr/(_ (subxx _)) => <- //; last exact: normal_norm.
  by rewrite subGcfker.
Qed.

(* This is Peterfalvi (12.2a), second part *)
Lemma tau_isometry  :
    {in 'Z[[seq 'chi_i | i in \bigcup_(chi <- calS) S_ chi], L^#], 
      isometry tau, to 'Z[irr G]}.
Proof.
apply: (sub_iso_to _ _ (Dade_Zisometry _)); last exact: zcharW.
have /subsetD1P[_ /setU1K <-] := FTsupp0_sub L.
move=> phi; rewrite zcharD1E big_tnth FTsupp0_type1 // => /andP[S_phi phi1nz].
rewrite zcharD1 {}phi1nz andbT setUC.
apply: zchar_trans_on phi S_phi => ? /imageP[i /bigcupP[j _ Sj_i] ->].
rewrite zchar_split irr_vchar /=.
by have [_ _ ->] := PF_12_2a (mem_tnth j (in_tuple calS)).
Qed.

(*Lemma calSUP i : reflect (i \in \bigcup_(chi <- calS) S_ chi).*)

(* This is Peterfalvi (12.2b) *)
(* Lemma FPtype1_subcoherent :  *)
(*   {R : 'CF(L) -> seq _ |  *)
(*     (subcoherent calS tau R) /\  *)
(*     exists R1 : 'CF(L) -> 2.-tuple _, forall i (phi := 'chi_i), *)
(*       i \in \bigcup_(chi <- calS) S_ chi -> *)
(*       [/\ (orthonormal (R1 phi)), *)
(*           (tau (phi - phi^%CF = (\sum_(mu <- R1 phi) mu)%CF) & *)
(*           forall psi, psi \in calS -> R psi = *)
(*             [seq i | phi <- S_ psi, i <- R1 phi] *)
(* ] *)
(* }. *)
(* Proof. *)
(* have nHL : H <| L by exact: gFnormal. *)
(* have U_S : uniq calS by exact: seqInd_uniq. *)
(* have vcS: {subset calS <= 'Z[irr L]} by exact: seqInd_vcharW. *)
(* have N_S: {subset calS <= character} by exact: seqInd_char. *)
(* have oSS: pairwise_orthogonal calS by exact: seqInd_orthogonal. *)
(* have [U_0S dotSS]:= pairwise_orthogonalP oSS. *)
(* have freeS := orthogonal_free oSS. *)
(* have nrS : ~~ has cfReal calS by apply: seqInd_notReal; rewrite ?mFT_odd. *)
(* have ccS : conjC_closed calS by exact:cfAut_seqInd. *)
(* have exR1 (i : {i | i \in \bigcup_(chi <- calS) S_ chi}) (phi := 'chi_(sval i)) : *)
(*   exists R1 : 2.-tuple _,  *)
(*   (orthonormal R1) && (tau (phi - phi^%CF == (\sum_(mu <- R1) mu)%CF). *)
(*   admit. *)
(* have sigR1 (i : {i | i \in \bigcup_(chi <- calS) S_ chi}) := sigW (exR1 i). *)


End Twelve2.

End PFTwelve.


