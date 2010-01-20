(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime binomial groups.
Require Import morphisms perm action automorphism normal zmodp cyclic.
Require Import gfunc pgroups nilpotent gprod center commutators sylow abelian.
Require Import maximal hall BGsection1 BGsection6.

(******************************************************************************)
(*   This file covers B & G, section 7, i.e., the proof of the Thompson       *)
(* Transitivity Theorem, as well as some generalisations used later in the    *)
(* proof.                                                                     *)
(*   This is the first section of the proof that applies to a (hypothetical)  *)
(* minimally simple odd group, so we also introduce at this point some        *)
(* infrastructure to carry over this assumption into the rest of the proof.   *)
(*   minSimpleOddGroupType == a finGroupType that ranges exactly over the     *)
(*                            elements of a minimal counter-example to the    *)
(*                            Odd Order Theorem.                              *)
(*                       G == the group of all the elements in a              *)
(*                            minSimpleOddGroupType (this is a local notation *)
(*                            that must be reestablished for each such Type). *)
(*                      'M == the set of all (proper) maximal subgroups of G  *)
(*                   'M(H) == the set of all elements of 'M that contain U    *)
(*                      'U == the set of all H such that 'M(H) contains a     *)
(*                            single (unique) maximal subgroup of G.          *)
(*               'SCN_n[p] == the set of all SCN subgroups of rank at least n *)
(*                            of all the Sylow p-subgroups of G.              *)
(*            |/|_H(A, pi) == the set of all pi-subgroups of H that are       *)
(*                            normalised by A.                                *)
(*             |/|*(A, pi) == the set of pi-subgroups of G, normalised by A,  *)
(*                            and maximal subject to this condition.          *)
(*    normed_constrained A == A is a nontrivial proper subgroup of G, such    *)
(*                            that for any proper subgroup X containing A,    *)
(*                            all Y in |/|_X(A, pi') lie in the pi'-core of X *)
(*                            (here pi is the set of prime divisors of #|A|). *)
(*                            This is Hypothesis 7.1 in B & G.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section InitialReduction.

Implicit Type gT : finGroupType.

Record minSimpleOddGroupMixin gT : Prop := MinSimpleOddGroupMixin {
  _ : odd #|[set: gT]|;
  _ : simple [set: gT];
  _ : ~~ solvable [set: gT];
  _ : forall M : {group gT}, M \proper [set: gT] -> solvable M
}.

Structure minSimpleOddGroupType := MinSimpleOddGroupType {
  minSimpleOddGroupType_base :> finGroupType;
  _ : minSimpleOddGroupMixin minSimpleOddGroupType_base
}.

Hypothesis IH_FT : minSimpleOddGroupType -> False.

Lemma minSimpleOdd_ind : forall gT (G : {group gT}), odd #|G| -> solvable G.
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT G *; rewrite ltnS => leGn oddG.
have oG: #|[subg G]| = #|G| by rewrite (isog_card (isog_subg G)).
apply/idPn=> nsolG; case: IH_FT; exists [finGroupType of subg_of G].
do [split; rewrite ?oG //=] => [||M].
- rewrite -(isog_simple (isog_subg _)); apply/simpleP; split=> [|H nsHG].
    by apply: contra nsolG; move/eqP->; rewrite abelian_sol ?abelian1.
  have [sHG _]:= andP nsHG; apply/pred2P; apply: contraR nsolG; case/norP=> ntH.
  rewrite eqEcard sHG -ltnNge (series_sol nsHG) => ltHG.
  by rewrite !IHn ?(oddSg sHG) ?quotient_odd ?(leq_trans _ leGn) ?ltn_quotient.
- by apply: contra nsolG => solG; rewrite -(sgvalEdom G) morphim_sol.
rewrite properEcard oG; case/andP=> sMG ltMG.
by apply: IHn (leq_trans ltMG leGn) (oddSg sMG _); rewrite oG.
Qed.

(* Temporary sanity check. *)
Lemma minSimpleOdd_prime : forall gT (G : {group gT}),
  odd #|G| -> simple G -> prime #|G|.
Proof.
move=> gT G oddG simpG.
have solG := minSimpleOdd_ind oddG.
have chsimG: charsimple G := minnormal_charsimple simpG.
have: is_abelem G := charsimple_solvable chsimG solG.
case/is_abelemP=> p p_pr; case/and3P=> pG cGG _.
case/simpleP: simpG => ntG simpG; have{pG ntG} [_ pG _] := pgroup_pdiv pG ntG.
case/Cauchy: pG => // x Gx oxp; move: p_pr; rewrite -{}oxp /order.
suffices: <[x]> <| G by case/simpG=> -> //; rewrite cards1.
by rewrite /normal andbC (sub_abelian_norm cGG) // cycle_subG.
Qed.

End InitialReduction.

Notation TheMinSimpleOddGroup gT :=
    [set: FinGroup.sort (FinGroup.base (minSimpleOddGroupType_base gT))]
  (only parsing).

Section MinSimpleOdd.

Variable gT : minSimpleOddGroupType.
Notation G := (TheMinSimpleOddGroup gT).

Lemma minSimple_odd : forall H : {group gT}, odd #|H|.
Proof. by move=> H; apply: (oddSg (subsetT H)); case: gT => ? []. Qed.

Lemma minSimple_simple : simple G.
Proof. by case: gT => ? []. Qed.

Lemma minSimple_nonSolvable : ~~ solvable G.
Proof. by case: gT => ? []. Qed.

Lemma proper_minSimple_sol : forall M : {group gT}, M \proper G -> solvable M.
Proof. by case: gT => ? []. Qed.

Lemma minSimple_nonAbelian : ~~ abelian G.
Proof. apply: contra minSimple_nonSolvable; exact: abelian_sol. Qed.

Lemma quotient_minSimple_odd : forall M H : {group gT}, odd #|M / H|.
Proof. by move=> M H; rewrite quotient_odd ?minSimple_odd. Qed.

Lemma proper_norm_minSimple : forall H : {group gT},
  H :!=: 1 -> H \proper G -> 'N(H) \proper G.
Proof.
move=> H ntH; rewrite !properT; apply: contra; move/eqP=> nHG; apply/eqP.
move/eqP: ntH; case/simpleP: minSimple_simple => _; case/(_ H) => //.
by rewrite /= -nHG normalG.
Qed.

Lemma trivg_cent_minSimple : 'C(G) = 1.
Proof.
apply/eqP; apply: contraR minSimple_nonAbelian => ntC.
rewrite /abelian subTset /= eqEproper subsetT /=; apply/negP=> prC.
have:= proper_norm_minSimple ntC prC.
by rewrite /proper subsetT norms_cent ?normG.
Qed.

Lemma proper_cent_minSimple : forall H : {group gT},
  H :!=: 1 -> 'C(H) \proper G.
Proof.
move=> H; case: (eqsVneq H G) => [-> | ].
  by rewrite trivg_cent_minSimple properT eq_sym.
rewrite -properT => prH ntH; apply: sub_proper_trans (cent_sub H) _.
exact: proper_norm_minSimple.
Qed.

Lemma quotient_minSimple_sol : forall M H : {group gT},
  H :!=: 1 -> solvable (M / H).
Proof.
move=> M H ntH; case: (eqsVneq H G) => [-> |].
  rewrite [_ / _](trivgP _) ?abelian_sol ?abelian1 //.
  by rewrite quotient_sub1 ?normsG ?subsetT.
rewrite -properT => prH; rewrite -quotientInorm morphim_sol //.
apply: solvableS (subsetIr _ _) (proper_minSimple_sol _).
by rewrite proper_norm_minSimple.
Qed.


Definition max_groups := [set M : {group gT} | maximal M G].
Definition max_supgroups (H : {set gT}) := [set M \in max_groups | H \subset M].
Definition uniq_max_subgroups := [set U : {group gT} | #|max_supgroups U| <= 1].
Definition minSimple_SCN_at n p := \bigcup_(P \in 'Syl_p(G)) 'SCN_n(P).

Lemma normal_max_group : forall M H : {group gT},
  M \in max_groups -> H <| M -> H :!=: 1 -> 'N(H) = M.
Proof.
move=> M H; rewrite inE; case/maxgroupP=> prM maxM; case/andP=> sHM nHM ntH.
apply: maxM nHM; rewrite proper_norm_minSimple //.
exact: sub_proper_trans prM.
Qed.

Lemma max_supgroupS : forall H K : {set gT},
  H \subset K -> max_supgroups K \subset max_supgroups H.
Proof.
move=> H K sHK; apply/subsetP=> M; rewrite !inE; case/andP=> ->.
exact: subset_trans.
Qed.

Lemma uniq_maxP : forall M1 M2 U : {group gT},
  U \in uniq_max_subgroups ->
  M1 \in max_supgroups U -> M2 \in max_supgroups U -> M1 = M1.
Proof.
move=> M1 M2 U uU M1_U M2_U; have:= uU.
by rewrite inE (cardD1 M1) (cardD1 M2) M1_U inE /= M2_U; case: eqP.
Qed.

Lemma uniq_maxS : forall U V : {group gT},
  U \subset V -> U \in uniq_max_subgroups -> V \in uniq_max_subgroups.
Proof.
move=> U V sUV; rewrite !inE; apply: leq_trans.
by rewrite subset_leq_card ?max_supgroupS.
Qed.

End MinSimpleOdd.

Notation "''M'" := (max_groups _) (at level 8, format "''M'") : group_scope.
Notation "''M' ( H )" := (max_supgroups H)
 (at level 8, format "''M' ( H )") : group_scope.
Notation "''U'" := (uniq_max_subgroups _) (at level 8) : group_scope.
Notation "''SCN_' n [ p ]" := (minSimple_SCN_at _ n p)
  (at level 8, n at level 2, format "''SCN_' n [ p ]") : group_scope.

Section Hypothesis7_1.

Variable gT : finGroupType.

Definition normed_pgroups (X A : {set gT}) pi :=
  [set Y : {group gT} | pi.-subgroup(X) Y && (A \subset 'N(Y))].

Definition max_normed_pgroups (A : {set gT}) pi :=
  [set Y | [max Y | pi.-group Y && (A \subset 'N(Y))]].

Inductive normed_constrained (A : {set gT}) :=
  NormedConstrained (pi := \pi(#|A|)) of A != 1 & A \proper setT
  & forall X Y : {group gT},
      A \subset X -> X \proper setT -> Y \in normed_pgroups X A pi^' -> 
    Y \subset 'O_pi^'(X).

End Hypothesis7_1.

Notation "|/|_ X ( A ; pi )" := (normed_pgroups X A pi)
  (at level 8, X at level 2, format "|/|_ X ( A ;  pi )") : group_scope.
Notation "|/|* ( A ; pi )" := (max_normed_pgroups A pi)
  (at level 8, format "|/|* ( A ;  pi )") : group_scope.

Section Seven.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types H P Q R K M A : {group gT}.
Implicit Type p q : nat.

Section NormedConstrained.

Variables (q : nat) (A : {group gT}).
Let pi := \pi(#|A|).
Let K := 'O_pi^'('C(A)).

Lemma norm_acts_max_norm : forall P, [acts 'N(P), on |/|*(P; q) | 'JG].
Proof.
move=> P; apply/subsetP=> z Nz; rewrite !inE; apply/subsetP=> Q; rewrite !inE.
case/maxgroupP=> qQ maxQ; apply/maxgroupP; rewrite pgroupJ norm_conj_norm //.
split=> // Y; rewrite sub_conjg /= => qY; move/maxQ=> <-; rewrite ?conjsgKV //.
by rewrite pgroupJ norm_conj_norm ?groupV.
Qed.

Lemma trivg_max_norm : forall P, 1%G \in |/|*(P; q) -> |/|*(P; q) = [set 1%G].
Proof.
move=> P max1; apply/eqP; rewrite eqEsubset sub1set max1 andbT.
apply/subsetP=> Q; rewrite !inE -val_eqE /= in max1 *.
by case/maxgroupP: max1 => _ max1; move/maxgroupp; move/max1->; rewrite ?sub1G.
Qed.

Let nsKC : K <| 'C(A) := pcore_normal _ _.

Lemma cent_core_acts_max_norm : [acts K, on |/|*(A; q) | 'JG].
Proof.
apply: subset_trans (subset_trans (pcore_sub _ _) (cent_sub A)) _.
exact: norm_acts_max_norm.
Qed.
Let actsKmax := actsP cent_core_acts_max_norm.

Hypotheses (cstrA : normed_constrained A) (pi'q : q \notin pi).
Let hyp71 : forall H R,
  A \subset H -> H \proper G -> R \in |/|_H(A; pi^') -> R \subset 'O_pi^'(H).
Proof. by case cstrA. Qed.

Lemma normed_constrained_Hall : pi^'.-Hall('C(A)) K.
Proof.
have [_ ntA prA _] := cstrA; rewrite -[setT]/G in prA.
rewrite /pHall pcore_pgroup pcore_sub pnatNK /=.
rewrite -card_quotient ?bgFunc_norm //= -/K.
apply/pgroupP=> p p_pr; case/Cauchy=> // Kx; case/morphimP=> x Nx Cx ->{Kx}.
rewrite /order -quotient_cycle //= -/K => def_p; apply/idPn=> pi'p.
have [P sylP] := Sylow_exists p <[x]>; have [sPx pP _]:= and3P sylP.
suffices: P \subset K.
  have nKP: P \subset 'N(K) by rewrite (subset_trans sPx) ?cycle_subG.
  rewrite -quotient_sub1 //= -/K (sameP trivgP eqP) trivg_card1.
  rewrite (card_Hall (morphim_pHall _ nKP sylP)) def_p part_pnat ?pnat_id //.
  by case: eqnP p_pr => // ->.
suffices sP_pAC: P \subset 'O_pi^'(A <*> 'C(A)).
  rewrite (subset_trans sP_pAC) ?pcore_max ?pcore_pgroup //.
  rewrite /normal (char_norm_trans (pcore_char _ _)) ?normsG ?mulgen_subr //.
  rewrite andbT -quotient_sub1; last first.
    rewrite (subset_trans (pcore_sub _ _)) // mulgen_subG normG cents_norm //.
    by rewrite centsC.
  rewrite /= -(setIidPr (pcore_sub _ _)) quotientGI ?mulgen_subr //=.
  rewrite {1}cent_mulgenEr // quotient_mulg coprime_TIg // coprime_morph //.
  by rewrite coprime_pi' ?cardG_gt0 //= -/pi [pnat _ _]pcore_pgroup.
apply: hyp71; first exact: mulgen_subl.
  apply: sub_proper_trans (proper_norm_minSimple ntA prA).
  by rewrite mulgen_subG normG cent_sub.
have sPC: P \subset 'C(A) by rewrite (subset_trans sPx) ?cycle_subG.
rewrite inE /psubgroup cents_norm 1?centsC // andbT.
rewrite (subset_trans sPC) ?mulgen_subr //=.
by apply: sub_in_pnat pP => p' _; move/eqnP->.
Qed.
Let hallK := normed_constrained_Hall.

Lemma normed_constrained_meet_trans : forall Q1 Q2 H,
    A \subset H -> H \proper G -> Q1 \in |/|*(A; q) -> Q2 \in |/|*(A; q) ->
    Q1 :&: H != 1 -> Q2 :&: H != 1 ->
  exists2 k, k \in K & Q2 :=: Q1 :^ k.
Proof.
move=> Q1 Q2 H; move: {2}_.+1 (ltnSn (#|G| - #|Q1 :&: Q2|)) => m.
elim: m => // m IHm in H Q1 Q2 * => geQ12m sAH prHG maxQ1 maxQ2 ntHQ1 ntHQ2.
have:= maxQ1; rewrite inE; case/maxgroupP; case/andP=> qQ1 nQ1A maxQ1P.
have:= maxQ2; rewrite inE; case/maxgroupP; case/andP=> qQ2 nQ2A maxQ2P.
have prQ12: Q1 :&: Q2 \proper G.
  rewrite properT; apply: contra (minSimple_nonSolvable gT); move/eqP <-.
  by apply: pgroup_sol (pgroupS _ qQ1); rewrite subsetIl.
wlog defH: H prHG sAH ntHQ1 ntHQ2 / Q1 :&: Q2 != 1 -> H :=: 'N(Q1 :&: Q2).
  case: (eqVneq (Q1 :&: Q2) 1) => [-> | ntQ12] IH.
    by apply: (IH H) => //; case/eqP.
  apply: (IH 'N(Q1 :&: Q2)%G); rewrite ?normsI ?proper_norm_minSimple //;
    apply: contra ntQ12; rewrite -!subG1; apply: subset_trans;
    by rewrite subsetI normG (subsetIl, subsetIr).
pose L := 'O_pi^'(H); have sLH: L \subset H := pcore_sub _ _.
have [nLA coLA solL]: [/\ A \subset 'N(L), coprime #|L| #|A| & solvable L].
- rewrite (char_norm_trans (pcore_char _ _)) ?normsG //.
  rewrite coprime_sym coprime_pi' ?cardG_gt0 ?[pnat _ _]pcore_pgroup //.
  by rewrite (solvableS sLH) ?proper_minSimple_sol.
have Qsyl: forall Q, Q \in |/|*(A; q) -> Q :&: H != 1 ->
  exists R : {group _}, [/\ q.-Sylow(L) R, A \subset 'N(R) & Q :&: H \subset R].
- move=> Q; rewrite inE; case/maxgroupP; case/andP=> qQ nQA _ ntQH.
  have qQH: q.-group (Q :&: H) by rewrite (pgroupS _ qQ) ?subsetIl.
  have nQHA: A \subset 'N(Q :&: H) by rewrite normsI // normsG.
  apply: coprime_Hall_subset => //; apply: (hyp71) => //.
  rewrite inE nQHA /psubgroup subsetIr andbT.
  by apply: sub_in_pnat qQH => p _; move/eqnP->.
have [R1 [sylR1 nR1A sQR1]] := Qsyl _ maxQ1 ntHQ1.
have [R2 [sylR2 nR2A sQR2]] := Qsyl _ maxQ2 ntHQ2.
have [h Ch defR2] := coprime_Hall_trans nLA coLA solL sylR2 nR2A sylR1 nR1A.
have{Ch} [Hh Kh]: h \in H /\ h \in K.
  case/setIP: Ch => Lh Ch; rewrite (subsetP sLH) //.
  rewrite (mem_normal_Hall hallK (pcore_normal _ _)) //.
  by rewrite (mem_p_elt _ Lh) ?pcore_pgroup.
have [Q3 maxQ3 sR2Q3]: exists2 Q3, Q3 \in |/|*(A; q) & R2 \subset Q3.
  pose nAq Q := q.-group Q && (A \subset 'N(Q)).
  have: nAq R2 by rewrite /nAq (pHall_pgroup sylR2).
  by case/maxgroup_exists => Q3 maxQ3 sR2Q3; exists Q3; rewrite ?inE.
have maxQ1h: (Q1 :^ h)%G \in |/|*(A; q) by rewrite actsKmax.
case: (eqsVneq Q1 Q2) => [| neQ12]; first by exists 1; rewrite ?group1 ?conjsg1.
have ntHQ3: Q3 :&: H != 1.
  apply: contra ntHQ2; rewrite -!subG1; apply: subset_trans.
  by rewrite subsetI subsetIr (subset_trans sQR2).
have ntHQ1h: (Q1 :^ h) :&: H != 1.
  by move: ntHQ1; rewrite !trivg_card1 -(cardJg _ h) conjIg (conjGid Hh).
suff [prI1 prI2]: Q1 :&: Q2 \proper Q1 :&: R1 /\ Q1 :&: Q2 \proper Q2 :&: R2.
  have: #|G| - #|(Q1 :^ h) :&: Q3| < m.
    rewrite ltnS in geQ12m; apply: leq_trans geQ12m.
    rewrite ltn_sub2l ?(proper_card prQ12) // -(cardJg _ h) proper_card //.
    by rewrite (proper_sub_trans _ (setIS _ sR2Q3)) // defR2 -conjIg properJ.
  have: #|G| - #|Q3 :&: Q2| < m.
    rewrite ltnS in geQ12m; apply: leq_trans geQ12m.
    rewrite ltn_sub2l ?proper_card // (proper_sub_trans prI2) //.
    by rewrite setIC setISS.
  case/(IHm H) => // k2 Kk2 defQ2; case/(IHm H) => // k3 Kk3 defQ3.
  by exists (h * k3 * k2); rewrite ?groupM ?conjsgM // -defQ3.
case: (eqVneq (Q1 :&: Q2) 1) => [-> | ntQ12].
  rewrite !proper1G; split; [apply: contra ntHQ1 | apply: contra ntHQ2];
    by rewrite -!subG1; apply: subset_trans; rewrite subsetI subsetIl.
rewrite -(setIidPr (subset_trans (pHall_sub sylR1) sLH)) setIA.
rewrite -(setIidPr (subset_trans (pHall_sub sylR2) sLH)) setIA.
rewrite (setIidPl sQR1) (setIidPl sQR2) {}defH //.
rewrite !properE !(subsetI (Q1 :&: Q2)) subsetIl subsetIr !normG /=.
split; apply: contra neQ12.
  move/(nilpotent_sub_norm (pgroup_nil qQ1) (subsetIl _ _)); move/esym.
  by move/setIidPl=> sQ12; rewrite (maxQ1P Q2) ?qQ2.
move/(nilpotent_sub_norm (pgroup_nil qQ2) (subsetIr _ _)); move/esym.
by move/setIidPr=> sQ21; rewrite (maxQ2P Q1) ?qQ1.
Qed.

Theorem normed_constrained_rank3_trans :
  'r('Z(A)) >= 3 -> [transitive K, on |/|*(A; q) | 'JG].
Proof.
case/rank_geP=> B.
case/nElemP=> p; rewrite !inE -andbA; case/and3P=> sBZ abelB mB3.
have p_pr: prime p by move: mB3; rewrite lognE; case: and3P => [[]|//].
rewrite subsetI in sBZ; case/andP: sBZ => sBA cAB.
have [_ abB _] := and3P abelB.
have q'B: forall Q, q.-group Q -> coprime #|Q| #|B|.
  move=> Q qQ; apply: coprimegS sBA _; rewrite coprime_sym coprime_pi' //.
  by apply: sub_in_pnat qQ => q' _; move/eqnP->.
have [Q1 maxQ1]: exists Q1, Q1 \in |/|*(A; q).
  have: exists Q1 : {group gT}, q.-group Q1 && (A \subset 'N(Q1)).
    by exists 1%G; rewrite pgroup1 norms1.
  by case/ex_maxgroup=> Q1; exists Q1; rewrite inE.
apply/imsetP; exists Q1 => //; apply/setP=> Q2.
apply/idP/imsetP=> [maxQ2|[k Kk] ->]; last by rewrite actsKmax.
have:= maxQ1; rewrite inE; move/maxgroupp; case/andP=> qQ1 nQ1A.
have:= maxQ2; rewrite inE; move/maxgroupp; case/andP=> qQ2 nQ2A.
case: (eqVneq Q1 1%G) => [trQ1 | ntQ1].
  exists 1; rewrite ?group1 // act1; apply/eqP.
  by rewrite trivg_max_norm -trQ1 // inE in maxQ2.
case: (eqVneq Q2 1%G) => [trQ2 | ntQ2].
  by case/negP: ntQ1; rewrite trivg_max_norm -trQ2 // inE in maxQ1 *.
have [C]: exists C : {group gT}, [&& 'C_Q1(C) != 1, C <| B & cyclic (B / C)].
  apply/existsP; apply: contraR ntQ1; rewrite negb_exists; move/forallP=> trQ1.
  have nQ1B := subset_trans sBA nQ1A.
  rewrite (coprime_abelian_gen_cent _ nQ1B) ?q'B //.
  rewrite big1 //= => C; case/andP=> cycC nsCB; apply/eqP.
  by have:= trQ1 C; rewrite cycC nsCB !andbT negbK.
case/and3P=> ntCQ1 nsCB cycBC; have [sCB nCB]:= andP nsCB.
have{mB3} ncycC: ~~ cyclic C.
  apply/cyclicP=> [[x defC]]; have Bx: x \in B by rewrite -cycle_subG -defC.
  have maxB: forall y, y \in B -> logn p #[y] <= 1.
    move=> y By; case/abelemP: abelB => // _; move/(_ y By) => yp1.
    by rewrite -(pfactorK 1 p_pr) dvdn_leq_log ?prime_gt0 // order_dvdn yp1.
  case/cyclicP: cycBC => Cy defBC; have: Cy \in B / C by rewrite defBC cycle_id.
  case/morphimP=> y Ny By defCy; rewrite {Cy}defCy -quotient_cycle // in defBC.
  have:= leq_add (maxB x Bx) (maxB y By); rewrite leqNgt -(eqP mB3); case/negP.
  rewrite -(quotientGK nsCB) defBC quotientK ?cycle_subG // defC.
  rewrite -logn_mul // mul_cardG /= -defC -?norm_mulgenEr ?cycle_subG //.
  by rewrite logn_mul ?leq_addr ?cardG_gt0.
have [z]: exists z, (z \in C^#) && ('C_Q2[z] != 1).
  apply/existsP; apply: contraR ntQ2; rewrite negb_exists; move/forallP=> trQ2.
  have nQ2C := subset_trans sCB (subset_trans sBA nQ2A).
  rewrite (coprime_abelian_gen_cent1 _ ncycC nQ2C) ?(abelianS sCB) //.
    by rewrite big1 //= => z Cz; apply/eqP; have:= trQ2 z; rewrite Cz negbK.
  by rewrite (coprimegS sCB) ?q'B.
rewrite 2!inE -andbA; case/and3P=> ntz Cz ntzQ2.
have prCz: 'C[z] \proper G.
  by rewrite -cent_set1 -cent_gen proper_cent_minSimple ?cycle_eq1.
have sACz: A \subset 'C[z].
  by rewrite -cent_set1 centsC sub1set (subsetP cAB) ?(subsetP sCB).
have [|//|k Kk defQ2]:= normed_constrained_meet_trans sACz prCz maxQ1 maxQ2.
  apply: contra ntCQ1; rewrite -!subG1; apply: subset_trans.
  by rewrite setIS //= -cent_set1 centS // sub1set.
exists k => //; exact: val_inj.
Qed.

Lemma normed_constrained_rank2_trans :
  q %| #|'C(A)| -> 'r('Z(A)) >= 2 -> [transitive K, on |/|*(A; q) | 'JG].
Proof.
move=> qC; case/rank_geP=> B EnZ_B.
have{EnZ_B} [sBZ ncycB]: B \subset 'Z(A) /\ ~~ cyclic B.
  case/nElemP: EnZ_B => p; rewrite !inE -andbA; case/and3P=> sBZ abelB mB2.
  split=> //; apply: contraL (leqnn 2); rewrite -leqNgt -(eqP mB2).
  case/cyclicP=> x defB; case p_pr: (prime p); last by rewrite lognE p_pr.
  case/abelemP: abelB => // _; move/(_ x) => xp1.
  rewrite -(pfactorK 1 p_pr) dvdn_leq_log ?prime_gt0 // defB order_dvdn xp1 //.
  by rewrite defB cycle_id.
rewrite subsetI in sBZ; case/andP: sBZ => sBA cAB.
have abB: abelian B by exact: subset_trans cAB (centS _).
have [R0 sylR0] := Sylow_exists q 'C(A); have [cAR0 qR0 _] := and3P sylR0.
have [R maxR sR0R]: exists2 R, R \in |/|*(A; q) & R0 \subset R.
  suff [R]: {R | [max R | q.-group R && (A \subset 'N(R))] & R0 \subset R}.
    by exists R; rewrite 1?inE.
  by apply: maxgroup_exists; rewrite qR0 cents_norm // centsC.
have:= maxR; rewrite inE; case/maxgroupP; case/andP=> qR nRA maxRP.
apply/imsetP; exists R => //; apply/setP=> Q.
apply/idP/imsetP=> [maxQ|[k Kk] ->]; last by rewrite actsKmax.
have:= maxQ; rewrite inE; case/maxgroupP; case/andP=> qQ nQA maxQP.
case: (eqVneq 'C_R(A) 1) => [tiRC| ntRC].
  have: R0 :==: 1 by rewrite -subG1 -tiRC subsetI sR0R.
  rewrite trivg_card1 -dvdn1 (card_Hall sylR0) p_part.
  case q_pr: (prime q) => [] => [|_].
    by rewrite pfactor_dvdn // logn1 lognE q_pr qC cardG_gt0.
  exists 1; rewrite ?group1 //=; apply: val_inj; rewrite /= conjsg1.
  apply: etrans (_ : 1 = _); apply/eqP; rewrite ?(eq_sym 1) trivg_card1.
    by rewrite -(part_pnat qQ) p_part lognE q_pr.
  by rewrite -(part_pnat qR) p_part lognE q_pr.
have ntR: R :!=: 1.
  by apply: contra ntRC; rewrite -!subG1 => R1; rewrite subIset ?R1.
have ntQ: Q :!=: 1.
  by apply: contra ntR; move/eqP=> defQ; rewrite maxQP ?defQ ?sub1G ?qR.
have [z]: exists z, (z \in B^#) && ('C_Q[z] != 1).
  apply/existsP; apply: contraR ntQ; rewrite negb_exists; move/forallP=> trQ.
  have nQB := subset_trans sBA nQA.
  rewrite (coprime_abelian_gen_cent1 _ ncycB nQB) //; last first.
    rewrite (coprimegS sBA) // coprime_sym coprime_pi' //. 
    by apply: sub_in_pnat qQ => q' _; move/eqnP->.
  by rewrite big1 //= => z Cz; apply/eqP; have:= trQ z; rewrite Cz negbK.
rewrite 2!inE -andbA; case/and3P=> ntz Bz ntzQ.
have prCz: 'C[z] \proper G.
  by rewrite -cent_set1 -cent_gen proper_cent_minSimple ?cycle_eq1.
have sACz: A \subset 'C[z].
  by rewrite -cent_set1 centsC sub1set (subsetP cAB).
have [|//|k Kk defQ2]:= normed_constrained_meet_trans sACz prCz maxR maxQ.
  apply: contra ntRC; rewrite -!subG1; apply: subset_trans.
  by rewrite setIS //= -cent_set1 centS // sub1set (subsetP sBA).
exists k => //; exact: val_inj.
Qed.

Theorem normed_trans_superset : forall P : {group gT},
    A <|<| P -> pi.-group P -> [transitive K, on |/|*(A; q) | 'JG] ->
 [/\ 'C_K(P) = 'O_pi^'('C(P)),
     [transitive 'O_pi^'('C(P)), on |/|*(P; q) | 'JG],
     |/|*(P; q) \subset |/|*(A; q)
   & {in |/|*(P; q), forall Q,
         P :&: 'N(P)^`(1) \subset 'N(Q)^`(1)
      /\ 'N(P) = 'C_K(P) * 'N_('N(P))(Q)}].
Proof.
move=> P snAP piP trnK.
have defK: forall B : {group gT}, A \subset B -> 'C_K(B) = 'O_pi^'('C(B)).
  move=> B sAB; apply/eqP; rewrite eqEsubset {1}setIC pcoreS ?centS //.
  rewrite subsetI pcore_sub (subset_normal_Hall _ hallK) ?pcore_normal //.
  by rewrite /psubgroup pcore_pgroup (subset_trans (pcore_sub _ _)) ?centS.
suffices [trnKP smnPA]: [transitive 'O_pi^'('C(P)), on |/|*(P; q) | 'JG]
                        /\ |/|*(P; q) \subset |/|*(A; q).
- set KP := 'O_pi^'('C(P)) in trnKP *; rewrite (defK _ (subnormal_sub snAP)).
  have nsKPN: KP <| 'N(P) := char_normal_trans (pcore_char _ _) (cent_normal _).
  split=> // Q maxQ; have defNP: KP * 'N_('N(P))(Q) = 'N(P).
    rewrite -(astab1JG Q) -normC; last by rewrite subIset 1?normal_norm.
    apply/(subgroup_transitiveP maxQ); rewrite ?normal_sub //=.
    by rewrite (atrans_supgroup _ trnKP) ?norm_acts_max_norm ?normal_sub.
  split=> //; move/prod_norm_coprime_subs_derI: defNP => -> //.
  - by rewrite subIset // orbC commgSS ?subsetIr.
  - by rewrite subsetI normG; rewrite inE in maxQ; case/andP: (maxgroupp maxQ).
  by rewrite /= (pnat_coprime piP (pcore_pgroup _ _)).
elim: {P}_.+1 {-2}P (ltnSn #|P|) piP snAP => // m IHm P lePm piP snAP.
wlog{snAP} [B maxnB snAB]: / {B : {group gT} | maxnormal B P P & A <|<| B}.
  case/subnormalEr: snAP => [<- // | [D [snAD nDP prDP]]]; apply.
  have [B maxnB sDB]: {B : {group gT} | maxnormal B P P & D \subset B}.
    by apply: maxgroup_exists; rewrite prDP normal_norm.
  exists B => //; apply: subnormal_trans snAD (normal_subnormal _).
  by apply: normalS sDB _ nDP; case/andP: (maxgroupp maxnB); case/andP.
have [prBP nBP] := andP (maxgroupp maxnB); have sBP := proper_sub prBP.
have{lePm}: #|B| < m by exact: leq_trans (proper_card prBP) _.
case/IHm=> {IHm}// [|trnB smnBA]; first by rewrite (pgroupS sBP).
have{maxnB} abelPB: is_abelem (P / B).
  apply: charsimple_solvable (maxnormal_charsimple _ maxnB) _ => //.
  apply: quotient_sol (proper_minSimple_sol _).
  apply: sub_proper_trans nBP (proper_norm_minSimple _ _); last first.
    exact: proper_sub_trans prBP (subsetT _).
  rewrite -proper1G (proper_sub_trans _ (subnormal_sub snAB)) // proper1G.
  by case cstrA.
have{abelPB} [p p_pr pPB]: exists2 p, prime p & p.-group (P / B).
  by case/is_abelemP: abelPB => p p_pr; case/andP; exists p.
have{prBP} pi_p: p \in pi.
  case/pgroup_pdiv: pPB => [|_ pPB _].
    by rewrite -subG1 quotient_sub1 // proper_subn.
  by apply: pgroupP p_pr pPB; exact: quotient_pgroup.
pose S := |/|*(B; q); pose nq P Q := q.-group Q && (P \subset 'N(Q)).
have pi'S: pi^'.-nat #|S| := pnat_dvd (atrans_dvd trnB) (pcore_pgroup _ _).
have{pi'S} p'S: #|S| %% p != 0.
  by rewrite -prime_coprime // (pnat_coprime _ pi'S) ?pnatE.
have{p'S} [Q S_Q nQP]: exists2 Q, Q \in S & P \subset 'N(Q).
  have sTSB: setT \subset G / B by rewrite -quotientT quotientS ?subsetT.
  have modBE: {in P & S, forall x Q, ('JG %% B) Q (coset B x) = 'JG Q x}%act.
    move=> x Q Px; rewrite inE; move/maxgroupp; case/andP=> _ nQB.
    by rewrite /= modactE ?(subsetP nBP) ?afixJG ?setTI ?inE.
  have actsPB: [acts P / B, on S | 'JG %% B \ sTSB].
    apply/subsetP=> Bx; case/morphimP => x Nx Px ->{Bx}.
    rewrite !inE; apply/subsetP=> Q S_Q; rewrite inE /= modBE //.
    by rewrite (actsP (norm_acts_max_norm B)).
  move: p'S; rewrite (pgroup_fix_mod pPB actsPB); set nQ := #|_|.
  case: (posnP nQ) => [->|]; first by rewrite mod0n.
  rewrite lt0n; case/existsP=> Q; case/setIP=> Q_S fixQ; exists Q => //.
  apply/normsP=> x Px; apply: congr_group; have Nx := subsetP nBP x Px.
  by have:= afixP fixQ (coset B x); rewrite /= modBE ?mem_morphim //= => ->.
have{nQP}: nq P Q.
  by rewrite /nq nQP andbT; rewrite inE in S_Q; case/andP: (maxgroupp S_Q).
case/maxgroup_exists=> Q0 maxQ0 sQQ0; have [_ nQ0P] := andP (maxgroupp maxQ0).
have{maxQ0} mnP_Q0: Q0 \in |/|*(P; q) by rewrite inE.
case tr_mnP: (1%G \in |/|*(P; q)) => [|{Q S_Q sQQ0}].
  rewrite trivg_max_norm // ?inE in mnP_Q0 *; split.
    apply/imsetP; exists 1%G; rewrite ?set11 //.
    apply/eqP; rewrite eqEsubset sub1set orbit_refl.
    apply/subsetP=> R; case/imsetP=> z _ ->{R}.
    by rewrite inE -val_eqE /= conjs1g.
  rewrite (eqP mnP_Q0) subG1 in sQQ0; rewrite ((Q =P 1%G) sQQ0) in S_Q.
  by rewrite -(trivg_max_norm S_Q).
have sAB := subnormal_sub snAB; have sAP := subset_trans sAB sBP.
have smnP_S: |/|*(P; q) \subset S.
  apply/subsetP=> Q1 mnP_Q1; have ntQ1: Q1 :!=: 1.
    by apply: contraL mnP_Q1; move/eqP; move/val_inj->; rewrite tr_mnP.
  have:= mnP_Q1; rewrite inE; case/maxgroupP; case/andP=> qQ1 nQ1P mP_Q1.
  have prNQ1: 'N(Q1) \proper G.
    rewrite proper_norm_minSimple // properT.
    apply: contra (minSimple_nonSolvable gT); move/eqP <-.
    exact: pgroup_sol qQ1.
  have nQ1A: A \subset 'N(Q1) by rewrite (subset_trans sAP).
  have: nq B Q1 by rewrite /nq qQ1 (subset_trans sBP).
  case/maxgroup_exists=> Q2 nmB_Q2 sQ12; have S_Q2: Q2 \in S by rewrite inE.
  have [qQ2 nQ2B]:= andP (maxgroupp nmB_Q2).
  have qNQ2: q.-group 'N_Q2(Q1) by rewrite (pgroupS _ qQ2) ?subsetIl.
  have sNQ2_KN: 'N_Q2(Q1) \subset 'O_pi^'('N(Q1)).
    rewrite hyp71 // inE normsI ?norms_norm ?(subset_trans sAB nQ2B) //=.
    rewrite /psubgroup subsetIr andbT.
    by apply: sub_in_pnat qNQ2 => q' _; move/eqnP->.
  have [Q3 [sylQ3 nQ3P sQ13]]: exists Q3 : {group gT},
    [/\ q.-Sylow('O_pi^'('N(Q1))) Q3, P\subset 'N(Q3) & Q1 \subset Q3].
  - apply: coprime_Hall_subset=> //.
    + by rewrite (char_norm_trans (pcore_char _ _)) ?norms_norm.
    + by rewrite coprime_sym (pnat_coprime piP (pcore_pgroup _ _)).
    + by rewrite (solvableS (pcore_sub _ _)) ?proper_minSimple_sol.
    rewrite pcore_max /normal ?normG ?subxx //.
    by apply: sub_in_pnat qQ1 => q' _; move/eqnP->.
  have: 'N_Q2(Q1) \subset Q1.
    rewrite subEproper eq_sym eqEcard subsetI sQ12 normG /=.
    rewrite -{2}(mP_Q1 Q3) ?(pHall_pgroup sylQ3) // dvdn_leq ?cardG_gt0 //.
    by rewrite -(part_pnat qNQ2) (card_Hall sylQ3) partn_dvd ?cardSg.
  by move/(nilpotent_sub_norm (pgroup_nil qQ2) sQ12); move/val_inj <-.
split; last exact: subset_trans smnP_S smnBA.
apply/imsetP; exists Q0 => //; apply/setP=> Q2.
apply/idP/imsetP=> [maxQ2 | [k Pk ->]]; last first.
  rewrite (actsP (subset_trans _ (norm_acts_max_norm P)) k Pk) //.
  exact: subset_trans (pcore_sub _ _) (cent_sub _).
have [S_Q0 S_Q2]: Q0 \in S /\ Q2 \in S by rewrite !(subsetP smnP_S).
pose KB := 'O_pi^'('C(B)); pose KP := KB <*> P.
have pi'KB: pi^'.-group KB by exact: pcore_pgroup.
have nKB_P: P \subset 'N(KB).
  by rewrite (char_norm_trans (pcore_char _ _)) ?norms_cent.
have [k KBk defQ2]:= atransP2 trnB S_Q0 S_Q2.
have:= maxQ2; rewrite inE; move/maxgroupp; case/andP=> qQ2 nQ2P.
have hallP: pi.-Hall('N_KP(Q2)) P.
  have sPN: P \subset 'N_KP(Q2) by rewrite subsetI mulgen_subr.
  rewrite pHallE eqn_leq -{1}(part_pnat piP) dvdn_leq ?partn_dvd ?cardSg //.
  have ->: #|P| = #|KP|`_pi.
    rewrite /KP mulgenC norm_mulgenEl // coprime_cardMg ?(pnat_coprime piP) //.
    by rewrite partn_mul // part_pnat // part_p'nat // muln1.
  by rewrite sPN dvdn_leq ?partn_dvd ?cardSg ?cardG_gt0 ?subsetIl.
have hallPk: pi.-Hall('N_KP(Q2)) (P :^ k).
  rewrite pHallE -(card_Hall hallP) cardJg eqxx andbT subsetI /=.
  by rewrite defQ2 normJ conjSg conj_subG ?mulgen_subr // mem_gen // inE KBk.
have [gz]: exists2 gz, gz \in 'N_KP(Q2) & (P = P :^ k :^ gz)%G.
  apply: HallConj (solvableS (subsetIr _ _) _) hallP hallPk.
  apply: proper_minSimple_sol (proper_norm_minSimple _ _).
    by apply: contraL maxQ2; move/(Q2 =P _)->; rewrite tr_mnP.
  rewrite properT; apply: contra (minSimple_nonSolvable gT); move/eqP <-.
  exact: pgroup_sol qQ2.
rewrite [KP]norm_mulgenEr //= setIC -group_modr //= setIC -/KB.
case/imset2P=> g z; case/setIP=> KBg nQ2g Pz ->{gz} defP.
exists (k * g); last first.
  by apply: val_inj; rewrite /= conjsgM -(normP nQ2g) defQ2.
rewrite -defK // (subsetP (subsetIl _ 'C(B))) //= setIAC defK // -/KB.
rewrite -coprime_norm_cent 1?coprime_sym ?(pnat_coprime piP) //= -/KB.
rewrite inE groupM //; apply/normP.
by rewrite -{2}(conjsgK z P) (conjGid Pz) {2}defP /= !conjsgM conjsgK.
Qed.

End NormedConstrained.

Lemma plenght_1_normed_constrained : forall p A,
    A :!=: 1 -> A :=: [set x \in 'C(A) | x ^+ p == 1] ->
    (forall M, M \proper G -> p.-length_1 M) ->
  normed_constrained A.
Proof. Admitted. (* Requires B & G 6.7 *)

Lemma SCN_normed_constrained : forall p P A,
  p.-Sylow(G) P -> A \in 'SCN_2(P) -> normed_constrained A.
Proof.
move=> p P A sylP; rewrite 2!inE -andbA; case/and3P=> nsAP.
have [sAP nAP]:= andP nsAP; move/eqP=> defCA lt1mA.
have pP := pHall_pgroup sylP; have pA := pgroupS sAP pP.
have abA: abelian A by rewrite /abelian -{1}defCA subsetIr.
have prP: P \proper G.
  rewrite properT; apply: contra (minSimple_nonSolvable gT); move/eqP <-.
  exact: pgroup_sol pP.
have ntA: A :!=: 1 by rewrite -rank_gt0 ltnW.
pose pi : nat_pred := \pi(#|A|).
have [p_pr pdvA [r oApr]] := pgroup_pdiv pA ntA.
have{r oApr} def_pi: pi =i (p : nat_pred).
  by move=> p'; rewrite !inE oApr primes_exp // primes_prime ?inE.
have def_pi' := eq_negn def_pi; have defK := eq_pcore _ def_pi'.
pose Z := 'Ohm_1('Z(P)); have sZ_ZP: Z \subset 'Z(P) by exact: Ohm_sub.
have sZP_A: 'Z(P) \subset A by rewrite -defCA setIS ?centS.
have sZA := subset_trans sZ_ZP sZP_A.
have nsA1: 'Ohm_1(A) <| P by exact: (char_normal_trans (Ohm_char _ _)).
have [B [E2_B nsBP sBZ]]: exists B, [/\ B \in 'E_p^2(A), B <| P
                                      & B \subset Z \/ #|Z| = p /\ Z \subset B].
- have pZP: p.-group 'Z(P) by exact: pgroupS (center_sub _) pP.
  have pZ: p.-group Z by exact: pgroupS sZ_ZP pZP.
  have abelZ: p.-abelem Z by rewrite Ohm1_abelem ?abelian_center.
  have nsZP: Z <| P; last have [sZP nZP] := andP nsZP.
    by rewrite (char_normal_trans (Ohm_char _ _)) ?center_normal.
  case: (eqVneq Z 1).
    rewrite -(setIidPr sZ_ZP); move/TI_Ohm1; rewrite setIid.
    by move/(trivg_center_pgroup pP)=> P1; rewrite -subG1 -P1 sAP in ntA.
  case/(pgroup_pdiv pZ)=> _ _ [[|k] /=]; rewrite -/Z => oZ; last first.
    have: 2 <= 'r_p(Z) by rewrite p_rank_abelem // oZ pfactorK.
    case/p_rank_geP=> B; rewrite /= -/Z => Ep2Z_B; exists B.
    rewrite (subsetP (pnElemS _ _ sZA)) //.
    move: Ep2Z_B; rewrite !inE -andbA; case/andP=> sBZ _.
    split=> //; last by left.
    have sBZP := subset_trans sBZ sZ_ZP.
    rewrite /normal ?(subset_trans sBZP) ?center_sub ?cents_norm //.
    by rewrite centsC (subset_trans sBZP) ?subsetIr.
  have: ('Ohm_1(A) / Z) :&: 'Z(P / Z) != 1.
    rewrite nil_meet_Z // ?quotient_nil ?(pgroup_nil pP) ?quotient_normal //.
    rewrite -subG1 quotient_sub1 ?(subset_trans (normal_sub nsA1) nZP) //= -/Z.
    apply: contraL lt1mA => sA1Z; rewrite -leqNgt -rank_Ohm1.
    by rewrite (leq_trans (rankS sA1Z)) // (rank_abelem abelZ) oZ pfactorK.
  case/trivgPn=> Zx; case/setIP; case/morphimP=> x Nx A1x defZx Z_Zx ntZx.
  pose B := Z <*> <[x]>; rewrite -cycle_subG in Nx; exists [group of B].
  split; last by right; rewrite mulgen_subl.
    have sBA1: B \subset 'Ohm_1(A) by rewrite mulgen_subG cycle_subG OhmS.
    rewrite 2!inE (subset_trans _ (Ohm_sub 1 A)) //=.
    have abelB: p.-abelem B by rewrite (abelemS sBA1) ?Ohm1_abelem.
    have sZB: Z \subset B by rewrite mulgen_subl.
    rewrite abelB -(LaGrange sZB) oZ -card_quotient ?mulgen_subG ?normG //= -/Z.
    rewrite norm_mulgenEr // quotient_mulgr quotient_cycle -?cycle_subG //.
    have abelBZ: p.-abelem (B / Z) := morphim_abelem _ abelB.
    have B_Zx: Zx \in B / Z.
      by rewrite defZx mem_morphim -?cycle_subG ?mulgen_subr.
    have [_ oBx] := abelem_order_p abelBZ B_Zx ntZx.
    by rewrite -defZx -orderE oBx -expnSr pfactorK.
  rewrite /= -(quotientGK nsZP) /B norm_mulgenEr //= -quotientK //= -/Z.
  rewrite morphpre_normal ?quotientS // quotient_cycle -?cycle_subG // -defZx.
  case/setIP: Z_Zx => P_Zx cP_Zx.
  by rewrite /normal cents_norm ?andbT 1?centsC cycle_subG.
split; rewrite ?(sub_proper_trans sAP) // => X Y sAX prX.
rewrite inE defK -andbA (eq_pgroup _ def_pi'); case/and3P=> sYX p'Y nYA.
move: E2_B; rewrite 2!inE -andbA; case/and3P=> sBA abelB dimB2.
have [pB abB _] := and3P abelB.
have ntB: B :!=: 1 by case: (eqsVneq B 1) dimB2 => // ->; rewrite cards1 logn1.
have cBA: forall b, b \in B -> A \subset 'C[b].
  move=> b Bb; rewrite -cent_set1 centsC sub1set.
  by rewrite (subsetP abA) ?(subsetP sBA).
have solCB: forall b : gT, b != 1 -> solvable 'C[b].
  move=> b; rewrite -cycle_eq1; move/proper_cent_minSimple.
  by rewrite cent_gen cent_set1; exact: proper_minSimple_sol.
wlog{sAX prX} [b B'b defX]: X Y p'Y nYA sYX / exists2 b, b \in B^# & 'C[b] = X.
  move=> IH; have nYB := subset_trans sBA nYA.
  rewrite (coprime_abelian_gen_cent1 abB _ nYB); last first.
  - by rewrite coprime_sym (pnat_coprime pB).
  - apply: contraL dimB2; case/cyclicP=> x defB.
    have: x \in B by rewrite defB cycle_id.
    case/(abelem_order_p abelB)=> [|_]; first by rewrite -cycle_eq1 -defB.
    by rewrite /order -defB => ->; rewrite logn_prime ?eqxx.
  rewrite bigprodGE gen_subG; apply/bigcupsP=> b B'b.
  have [ntb Bb]:= setD1P B'b; have sYbY: 'C_Y[b] \subset Y := subsetIl _ _.
  have{IH} sYbKb: 'C_Y[b] \subset 'O_p^'('C[b]).
    rewrite IH ?(pgroupS sYbY) ?subsetIr //; last by exists b.
    by rewrite normsI // ?normsG ?cBA.
  have{sYbKb} sYbKXb: 'C_Y[b] \subset 'O_p^'('C_X(<[b]>)).
    apply: subset_trans (pcoreS _ (subsetIr _ _)).
    by rewrite /= cent_gen cent_set1 subsetI setSI.
  rewrite (subset_trans sYbKXb) // p'core_cent_pgroup ?proper_minSimple_sol //.
  rewrite /psubgroup ?(pgroupS _ pB) cycle_subG //.
  by rewrite (subsetP sAX) ?(subsetP sBA).
wlog Zb: b X Y defX B'b p'Y nYA sYX / b \in Z.
  move=> IH; case Zb: (b \in Z); first exact: IH Zb.
  case/setD1P: B'b => ntb Bb; have solX := solCB b ntb; rewrite defX in solX.
  case: sBZ => [sBZ | [oZ sZB]]; first by rewrite (subsetP sBZ) in Zb.
  have defB: Z * <[b]> = B.
    apply/eqP; rewrite eqEcard mulG_subG sZB cycle_subG Bb.
    have [_ obp] := abelem_order_p abelB Bb ntb.
    rewrite -(part_pnat pB) p_part //= (eqP dimB2) TI_cardMg -/#[_] ?oZ ?obp //.
    rewrite -obp in p_pr; case: (prime_subgroupVti [group of Z] p_pr) => //.
    by rewrite cycle_subG Zb.
  pose P1 := P :&: X; have sP1P: P1 \subset P := subsetIl _ _.
  have pP1 := pgroupS sP1P pP.
  have [P2 sylP2 sP12] := Sylow_superset (subsetIr _ _) pP1.
  have defP1: P1 = 'C_P(B).
    rewrite -defB centM /= -/Z setIA /cycle cent_gen cent_set1 defX.
    by rewrite [P :&: _](setIidPl _) // centsC (subset_trans sZ_ZP) ?subsetIr.
  have dimPP1: logn p #|P : P1| <= 1.
    by rewrite defP1 logn_quotient_cent_abelem ?normal_norm ?(eqP dimB2).
  have{dimPP1} nsP12: P1 <| P2.
    have pP2 := pHall_pgroup sylP2.
    have: logn p #|P2 : P1| <= 1.
      apply: leq_trans dimPP1; rewrite dvdn_leq_log //.
      rewrite -(dvdn_pmul2l (cardG_gt0 [group of P1])) !LaGrange ?subsetIl //.
      by rewrite -(part_pnat pP2) (card_Hall sylP) partn_dvd ?cardSg ?subsetT.
    rewrite -(pfactorK 1 p_pr) -pfactor_dvdn ?prime_gt0 // -p_part.
    rewrite part_pnat ?(pnat_dvd (dvdn_indexg _ _)) //=.
    case: (primeP p_pr) => _ dv_p; move/dv_p=> {dv_p}.
    case/pred2P=> oP21; first by rewrite -(index1g sP12 oP21) normal_refl.
    by rewrite (p_maximal_normal pP2) ?p_index_maximal ?oP21.
  have nsZP1_2: 'Z(P1) <| P2 by rewrite (char_normal_trans (center_char _)).
  have sZKp: Z \subset 'O_{p^', p}(X).
    suff: 'Z(P1) \subset 'O_{p^', p}(X).
      apply: subset_trans; rewrite subsetI {1}defP1 (subset_trans sZB).
        by rewrite (subset_trans sZ_ZP) ?subIset // orbC centS.
      by rewrite subsetI normal_sub.
    apply: odd_p_abelian_constrained sylP2 (abelian_center _) nsZP1_2 => //.
    exact: minSimple_odd.
  have coYZ: coprime #|Y| #|Z|.
    by rewrite oZ coprime_sym (pnat_coprime _ p'Y) ?pnatE ?inE.
  have nYZ := subset_trans sZA nYA.
  have <-: [~: Y, Z] * 'C_Y(Z) = Y.
    exact: coprime_cent_prod (solvableS sYX solX).
  set K := 'O_p^'(X); have [nKY nKZ]: Y \subset 'N(K) /\ Z \subset 'N(K).
    rewrite !(char_norm_trans (pcore_char _ _)) ?(subset_trans sZA) ?normsG //.
    by rewrite -defX cBA.
  rewrite mul_subG //.
    have coYZK: coprime #|Y / K| #|'O_p(X / K)|.
      by rewrite coprime_sym coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
    rewrite -quotient_sub1 ?comm_subG // -(coprime_TIg coYZK) subsetI.
    rewrite /= -quotient_pseries2 !quotientS ?commg_subl //.
    by rewrite (subset_trans (commgSS sYX sZKp)) ?commg_subr //= bgFunc_norm.
  have: 'O_p^'('C_X(Z)) \subset K.
    rewrite p'core_cent_pgroup // /psubgroup /pgroup oZ pnat_id //.
    by rewrite -defX (subset_trans sZA) ?cBA.
  apply: subset_trans; apply: subset_trans (pcoreS _ (subsetIr _ _)).
  have: cyclic Z by rewrite prime_cyclic ?oZ.
  case/cyclicP=> z defZ; have Zz: z \in Z by rewrite defZ cycle_id.
  rewrite subsetI setSI //= (IH z) ?subsetIr ?(pgroupS (subsetIl _ _)) //.
  - by rewrite defZ /= cent_gen cent_set1.
  - rewrite !inE -cycle_eq1 -defZ trivg_card_le1 oZ -ltnNge prime_gt1 //=.
    by rewrite (subsetP sZB).
  by rewrite normsI // norms_cent // cents_norm // centsC (subset_trans sZA).
set K := 'O_p^'(X); have nsKX: K <| X by exact: pcore_normal.
case/setD1P: B'b => ntb Bb.
have [sAX solX]: A \subset X /\ solvable X by rewrite -defX cBA ?solCB.
have sPX: P \subset X.
  by rewrite -defX -cent_set1 centsC sub1set; case/setIP: (subsetP sZ_ZP b Zb).
have [nKA nKY nKP]: [/\ A \subset 'N(K), Y \subset 'N(K) & P \subset 'N(K)].
  by rewrite !(subset_trans _ (normal_norm nsKX)).
have sylPX: p.-Sylow(X) P by exact: pHall_subl (subsetT _) sylP.
have sAKb: A \subset 'O_{p^', p}(X).
  exact: (odd_p_abelian_constrained (minSimple_odd _)) abA nsAP.
have coYZK: coprime #|Y / K| #|'O_p(X / K)|.
  by rewrite coprime_sym coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
have cYAq: A / K \subset 'C_('O_p(X / K))(Y / K).
  rewrite subsetI -quotient_pseries2 quotientS //= (sameP commG1P trivgP).
  rewrite /= -quotientR // -(coprime_TIg coYZK) subsetI /= -quotient_pseries2.
  rewrite !quotientS ?commg_subr // (subset_trans (commgSS sAKb sYX)) //.
  by rewrite commg_subl /= bgFunc_norm.
have cYKq: Y / K \subset 'C('O_p(X / K)).
  apply: coprime_nil_faithful_cent_stab => /=.
  - by rewrite (char_norm_trans (pcore_char _ _)) ?normsG ?quotientS.
  - by rewrite coprime_morphr ?(pnat_coprime (pcore_pgroup _ _)).
  - exact: pgroup_nil (pcore_pgroup _ _).
  apply: subset_trans (cYAq); rewrite -defCA -['C_P(A) / K](morphim_restrm nKP).
  rewrite injm_cent ?ker_restrm ?ker_coset ?morphim_restrm -?quotientE //.
    rewrite setIid (setIidPr sAP) setISS ?centS //.
    by rewrite pcore_sub_Hall ?morphim_pHall.
  by rewrite coprime_TIg ?(pnat_coprime _ (pcore_pgroup _ _)).
rewrite -quotient_sub1 //= -/K -(coprime_TIg coYZK) subsetI subxx /=.
rewrite -Fitting_eq_pcore ?trivg_pcore_quotient // in cYKq *.
apply: subset_trans (cent_sub_Fitting (quotient_sol _ solX)).
by rewrite subsetI quotientS.
Qed.

Theorem Thompson_transitivity : forall p q A,
    A \in 'SCN_3[p] -> q \in p^' ->
  [transitive 'O_p^'('C(A)), on |/|*(A; q) | 'JG].
Proof.
move=> p q A; case/bigcupP=> P; rewrite 2!inE => sylP; case/andP=> SCN_A mA3.
have [defZ def_pi']: 'Z(A) = A /\ \pi(#|A|)^' =i p^'.
  rewrite inE -andbA in SCN_A; case/and3P: SCN_A => sAP _; move/eqP=> defCA.
  case: (eqsVneq A 1) mA3 => [-> | ntA _].
    rewrite /rank big1_seq // => p1 _; rewrite /p_rank big1 // => E.
    by rewrite inE; case/andP; move/trivgP->; rewrite cards1 logn1.
  have [p_pr _ [k ->]] := pgroup_pdiv (pgroupS sAP (pHall_pgroup sylP)) ntA.
  split=> [|p1]; last by rewrite !inE primes_exp // primes_prime ?inE.
  by apply/eqP; rewrite eqEsubset subsetIl subsetI subxx -{1}defCA subsetIr.
rewrite -(eq_pcore _ def_pi') -def_pi' => pi'q.
apply: normed_constrained_rank3_trans; rewrite ?defZ //.
by apply: SCN_normed_constrained sylP _; rewrite inE SCN_A ltnW.
Qed.

End Seven.

