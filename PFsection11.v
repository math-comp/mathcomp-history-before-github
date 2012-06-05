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
(* This file covers Peterfalvi, Section 11: Maximal subgroups of Types        *)
(* III and IV.                                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory FinRing.Theory.

Section Eleven.

Lemma lbound_expn_odd_prime p q : 
   odd p -> odd q -> prime p -> prime q -> p != q -> 4 * q ^ 2 + 1 < p ^ q.
Proof.
case: p=> [|[|[|p]]] //; case: q=> [|[|[|[|[|q]]]]] //.
  case: p=> [|[|p]] // _ _ _ _ _.
  by have /(leq_trans _)-> : 5 ^ 3 <= p.+1.+4 ^ 3 by rewrite leq_exp2r.
set y := p.+3; set x := _.+4; move=> _ _ _ _ _.
have /(leq_trans _)-> //: 3 ^ x <= y ^ x by rewrite leq_exp2r.
rewrite {y}/x; elim: q => [| q IH] //.
rewrite [(3 ^ _)%N]expnS; set x := q.+1.+4 in IH |- *.
rewrite  -(ltn_pmul2l (_ : 0 < 3)) // in IH.
apply: (leq_trans _ IH); rewrite ltnS.
set X := _ + 1; have{X}->: X = 4 * x ^ 2 + (x * (7 * 1).+1 + (2 * 1 + 3))
  by rewrite /X; ring.
set X := (3 * _)%N; have{X}->: X = 4 * x ^ 2 +  (x * (7 * x) + (x * x + 3)) 
  by rewrite /X; ring.
rewrite leq_add2l; apply: leq_add; first by rewrite leq_mul2l ltn_mul2l.
by rewrite leq_add2r leq_mul.
Qed.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L N P Q R S T U V W : {group gT}.

Variables M U W1 : {group gT}.
Hypotheses (maxM : M \in 'M) (MtypeP: of_typeP M U W1).
Hypothesis Mtype34 : FTtype M \in pred2 3 4.
Let Mtypen5 : FTtype M != 5.
Proof. by case/orP: Mtype34=> /eqP->. Qed.
Let Mtype24 := compl_of_typeII_IV MtypeP maxM Mtypen5.
Let Mtypen2 : FTtype M != 2.
Proof. by case/orP: Mtype34=> /eqP->. Qed.

Local Notation H := (gval M)`_\F.
Local Notation W2 := 'C_H(gval W1).
Local Notation C := 'C_(gval U)(H).

Let p := #|W2|.
Let q := #|W1|.
Let H0 := Ptype_Fcore_kernel MtypeP.

Local Notation H0Cg := (gval H0 <*> C).
Local Notation H0C := [group of H0Cg].
Local Notation HCg := (H <*> C).
Local Notation HC := [group of HCg].

Let sol_M : solvable M := of_typeP_sol MtypeP.
Let sol_M': solvable M^`(1) := (solvableS (der_subS 0 _) sol_M).
Let M'_N_M : M^`(1) <| M := (der_normal _ _).
Let tau := Dade (FT_cDade_hyp maxM MtypeP).
Let R := FTtypeP_coh_base maxM MtypeP.
Let defM : M^`(1) ><| W1 = M. Proof. by have [[]] := MtypeP. Qed.
Let defHU : H ><| U = M^`(1). Proof. by have [_ []] := MtypeP. Qed.
Let chiefH0 : chief_factor M H0 H.
Proof. by have [] := Ptype_Fcore_kernel_exists maxM MtypeP Mtypen5. Qed.


Let subc_M : subcoherent (seqIndD M^`(1) M M^`(1) 1) tau R.
Proof.
suff{2}->: (M^`(1) = M`_\s)%G by apply: FTtypeP_subcoherent.
apply/val_eqP; rewrite /= /FTcore /=.
by case/orP: Mtype34=> /eqP->.
Qed.

Let ltH0H : H0 \proper H.
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.

Let sH0H : H0 \subset H. Proof. exact: proper_sub ltH0H. Qed.

Let nH0M : M \subset 'N(H0).
Proof. by case/andP: chiefH0 => /maxgroupp/andP[]. Qed.

Local Notation defHUW1 := (Ptype_Fcore_sdprod MtypeP).

Let nsCUW1 : C <| U <*> W1.
Proof.
have [_ sUW1M _ nHUW1 _] := sdprod_context defHUW1.
have [_ [_ _ nUW1 _] _ _ _] := MtypeP.
rewrite /normal subIset ?joing_subl // normsI //.
  by rewrite join_subG normG; have [_ []] := MtypeP.
by rewrite norms_cent.
Qed.

Let nsH0H : H0 <| H.
Proof. by rewrite /normal sH0H (subset_trans (Fcore_sub _)). Qed.

Let coherent H := 
  coherent (seqIndD M^`(1) M M^`(1) H) M^#
         (Dade_linear (FT_cDade_hyp maxM MtypeP)).

(* This is PF11.3 (should be changed when 10.8 is proved) *)
Lemma ncoH0C : coherent H0C -> coherent 1.
Proof.
have [nsHUM sW1M /mulG_sub[sHUM _] nHUW1 tiHUW1] := sdprod_context defM.
have [nsHHU sUHU /mulG_sub[sHHU sUM'] nHU tiHU] := sdprod_context defHU.
have [sHM sUM] := (subset_trans sHHU sHUM, subset_trans sUHU sHUM).
have sCM: C \subset M by rewrite subIset ?sUM.
have sH0C_M: H0C \subset M by rewrite /normal join_subG (subset_trans sH0H).
have [nH0C nH0_H0C] := (subset_trans sCM nH0M, subset_trans sH0C_M nH0M).
have sH0C_HC : H0C \subset HC by apply: genS (setSU _ _). 
have normal_hyps : [/\ 1 <| M, HC <| M & H0C <| M].
  suff nsH0C: H0C <| M.
    split=> //; first by exact: normal1.
    by rewrite /= -{1}(joing_idPl sH0H) -joingA normalY // gFnormal.
  rewrite /normal sH0C_M //= -{1}defM sdprodEY //=. 
  rewrite -defHU sdprodEY //= -joingA.
  rewrite join_subG andbC normsY ?(normal_norm nsCUW1) //=; last first.
    by rewrite (subset_trans _ nH0M) // join_subG sUM.
  apply/subsetP=> h HiH; rewrite inE.
  apply/subsetP=> g /imsetP [h1 H1iH0 ->].
  move: H1iH0; rewrite norm_joinEr // => /imset2P [g1 g2 G1iH0 G2iC->].
  rewrite conjMg; apply: mem_mulg; last first.
    suff->: g2 ^h = g2 by [].
    move: G2iC; rewrite conjgE inE => /andP[_ /centP /(_ _ HiH)->].
    by rewrite mulgA mulVg mul1g.
  case/normalP: nsH0H=> _ /(_ _ HiH)<-.
  by apply/imsetP; exists g1.
move=> coH0C.
apply: (bounded_seqIndD_coherent M'_N_M sol_M' subc_M normal_hyps)=> //.
- split=> //; first by apply/subsetP=> g; rewrite inE=> /eqP->.
  rewrite join_subG.
  case/andP: nsHHU=> -> _ /=.
  apply/subsetP=> g; rewrite inE=> /andP[GiU _].
  by apply: (subsetP sUM').
- apply: quotient_nil.
  suff/dprod_nil->: H \x C = HC.
    rewrite Fcore_nil /=.
    have/nilpotentS: C \subset U by apply: subsetIl.
    by apply; have[_ []]:= MtypeP.
  rewrite /= norm_joinEr /=.
    apply: (dprodE (subsetIr _ _)).
    apply/eqP; rewrite -subG1 -tiHU.
    by apply: setISS=> //; exact: subsetIl.
  apply: subset_trans (cent_sub _).
  by have[/dprodP[]]:= typeP_context MtypeP.
have/eqP->: #|M : (M^`(1))%G| == q.
  rewrite -(eqn_pmul2l (cardG_gt0 M^`(1))) (Lagrange sHUM).
  by move/sdprod_card: defM=> <-.
suff/eqP->: #|HC : H0C| == (p ^ q)%N.
  have pr_p : prime p.
    have:= typeII_IV_core maxM MtypeP Mtypen5.
    by rewrite (negPf Mtypen2); case.
  have pr_q : prime q by case Mtype24.
  apply: lbound_expn_odd_prime=> //; try by apply: mFT_odd.
  apply/eqP=> pEq.
  move: (cyclicTI_coprime (FT_cycTI_hyp MtypeP)); rewrite -/p -/q.
  rewrite pEq /coprime gcdnn => /eqP qE1.
  by move: pr_q; rewrite qE1.
rewrite /p -(typeIII_IV_core_prime maxM MtypeP) //.
have[_ _ <-] :=  Ptype_Fcore_factor_facts maxM MtypeP Mtypen5.
rewrite -(eqn_pmul2l (cardG_gt0 H0C)).
rewrite (Lagrange sH0C_HC) card_quotient; last by case/andP: nsH0H.
rewrite  /= !norm_joinEr ?TI_cardMg //.
- by rewrite mulnAC Lagrange //.
- apply/eqP; rewrite -subG1 -tiHU.
  by apply: setISS=> //; exact: subsetIl.
- apply/eqP; rewrite -subG1 -tiHU.
  by apply: setIS; exact: subsetIl.
apply: subset_trans (cent_sub _).
by have[/dprodP[]]:= typeP_context MtypeP.
Qed.

End Eleven.
