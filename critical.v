Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun ssralg bigops finset prime.
Require Import groups normal morphisms automorphism cyclic nilpotent.
Require Import commutators center pgroups sylow.

Import GroupScope.

Section CriticalThompson.

Variable gT : finGroupType.
Implicit Type M P: {group gT}.

(* Gorenstein 5.3.12 *)
Lemma crit_lem: 
  forall P M, p_group P ->  [max M of H | (H <| P) && abelian H] -> 'C_P(M) = M.
Proof.
move=> P M PgP; case/maxgroupP; case/andP=> NMP AM MM.
have: M \subset 'C_P(M) by rewrite subsetI (normal_sub NMP).
rewrite subEproper; case/orP => PMC; first by move/eqP: PMC.
set H := 'C_P(M); pose P' := P/M; pose H' := H/M.
have F1: H' <| P'.
  rewrite morphim_normal // /normal subIset ?subset_refl //=.
  apply/normsP=> p IpP; rewrite /H conjIg conjGid // -centJ. 
  by case/andP: NMP => _; move/normsP; move/(_ _ IpP) => ->.
have F2: ~ trivg H'.
  rewrite trivg_quotient; first by apply/negP; rewrite proper_subn.
  by rewrite subIset //; case/andP: NMP => _ ->.
have F3: ~ trivg(H' :&: 'Z(P')).
 apply/negP.
 (* why I can't apply directly nilpotent_meet_center? *)
 have GH': group_set H' by apply: morphim_groupset.
 rewrite -[H']/(Group GH': set _) nilpotent_meet_center //.
   by apply: nilpotent_quo; apply: (nilpotent_pgroup PgP).
 by apply/negP.
pose p := pdiv #|P|.
have F4: H \subset P by rewrite subIset // subset_refl.
have F5: prime p.
  rewrite prime_pdiv // (leq_trans _ (subset_leq_card F4)) //
          (leq_trans _ (proper_card PMC)) //.
  by apply: ltn_0group.
(* same pb *)
have GH'ZP': group_set (H' :&: 'Z(P')).
  have GH1: group_set H' by apply: morphim_groupset.
  have GH2: group_set 'Z(P') by apply: group_setI.
  apply: (@group_setI _ (Group GH1) (Group GH2)).
have: p %| #|Group GH'ZP'|.
  have: p.-group (Group GH'ZP').
    apply: (@pgroupS  _ _ [group of P']); last by apply: morphim_pgroup.
    by rewrite subIset // (normal_sub F1).
  case/pgroup_1Vpr=> [| [p_pr _ [k ->]]]; first by move/trivgP=> HH; case F3.
  by rewrite dvdn_mulr.
case/(Cauchy F5) => X'; rewrite in_setI; case/andP=> IX'H' IX'ZP' CX'.
have F6: <[X']> <| P'.
  rewrite /normal;  have->: <[X']> \subset P'.
    have GZP': group_set 'Z(P') by apply: group_setI.
    move: IX'ZP'; rewrite -['Z(P')]/(Group GZP': set _).
    by rewrite -cycle_subG subsetI; case/andP.
  rewrite norms_gen // cents_norm // centsC sub1set.
  by move: IX'ZP'; rewrite in_setI; case/andP.
case: (inv_quotientN NMP F6) => X /= DX SMX SXP.
move: CX' F5; rewrite /order DX.
suff->: X :=: M by rewrite trivial_quotient cards1 => <-.
rewrite MM // SXP; apply /setIidPl; symmetry; apply: center_cyclic_abelian.
suff F7: M \subset 'Z(X).
  apply: (isog_cyclic (third_isog F7 _ (center_normal _))).
    by apply: normalS NMP => //;  move/normal_sub: SXP.
  by rewrite cyclic_quo //= -DX;  apply/cyclicP; exists X'.
have F7: M \subset H by case/andP: PMC.
rewrite subsetI SMX centsC. 
have: <[X']> \subset H'.
  (* same pb *)
  have GH': group_set H' by apply: morphim_groupset.
  by rewrite -[H']/(Group GH': set _) cycle_subG.
rewrite DX quotientSGK //; first by rewrite subsetI; case/andP.
by rewrite normal_norm // (normalS _ _ NMP) //; case/andP: SXP.
Qed.

End CriticalThompson.

