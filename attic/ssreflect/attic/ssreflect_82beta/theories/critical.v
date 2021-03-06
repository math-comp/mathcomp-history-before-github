Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun ssralg bigops finset prime.
Require Import groups normal morphisms automorphism cyclic nilpotent.
Require Import commutators center pgroups sylow abelian.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GroupScope.

Section CriticalThompson.

Variable gT : finGroupType.
Implicit Type M P: {group gT}.

(* Gorenstein 5.3.12 *)
Lemma crit_lem : forall P M,
  p_group P -> [max M of H | (H <| P) && abelian H] -> 'C_P(M) = M.
Proof.
move=> P M PgP; case/maxgroupP; case/andP=> NMP AM MM.
have: M \subset 'C_P(M) by rewrite subsetI (normal_sub NMP).
rewrite subEproper; case/orP => PMC; first by move/eqP: PMC.
set H := 'C_P(M)%G; pose P' := (P / M)%G; pose H' := (H / M)%G.
have F1: H' <| P'.
  rewrite morphim_normal // /normal subIset ?subxx //=.
  apply/normsP=> p IpP; rewrite /H conjIg conjGid // -centJ.
  by case/andP: NMP => _; move/normsP; move/(_ _ IpP) => ->.
have F2: H' :!=: 1.
  by rewrite -subG1 quotient_sub1 ?proper_subn ?subIset // normal_norm.
have F3: H' :&: 'Z(P') != 1.
 apply: contra F2; move/eqP; move/nil_TI_Z=> -> //.
 by apply: quotient_nil; apply: (pgroup_nil PgP).
pose p := pdiv #|P|.
have F4: H \subset P by rewrite subIset // subxx.
have F5: prime p.
  rewrite prime_pdiv // (leq_trans _ (subset_leq_card F4)) //
          (leq_trans _ (proper_card PMC)) //.
  by exact: ltn_0group _ M.
have: p %| #|H' :&: 'Z(P')|; rewrite /P' /H' /H.
  have: p.-group (H' :&: 'Z(P')); rewrite /P' /H' /H.
    apply: (@pgroupS  _ _ (P/M)); last by apply: morphim_pgroup.
    by rewrite subIset // (normal_sub F1).
  case/pgroup_1Vpr=> [F3'| [p_pr _ [k ->]]]; last by rewrite dvdn_mulr.
  by case/eqP: F3.
case/(Cauchy F5) => X'; rewrite in_setI; case/andP=> IX'H' IX'ZP' CX'.
have F6: <[X']> <| P'.
  rewrite /normal;  have->: <[X']> \subset P'.
    move: IX'ZP'; rewrite /P' /H'/H.
    by rewrite -cycle_subG subsetI; case/andP.
  rewrite norms_gen // cents_norm // centsC sub1set.
  by move: IX'ZP'; rewrite in_setI; case/andP.
case: (inv_quotientN NMP F6) => X /= DX SMX SXP.
move: CX' F5; rewrite /order DX.
suff->: X :=: M by rewrite trivg_quotient cards1 => <-.
rewrite MM // SXP; apply /setIidPl; symmetry; apply: center_cyclic_abelian.
suff F7: M \subset 'Z(X).
  apply: (isog_cyclic (third_isog F7 _ (center_normal _))).
    by apply: normalS NMP => //;  move/normal_sub: SXP.
  by rewrite quotient_cyclic //= -DX;  apply/cyclicP; exists X'.
have F7: M \subset H by case/andP: PMC.
rewrite subsetI SMX centsC.
have: <[X']> \subset H'.
  by rewrite /H' /H cycle_subG.
rewrite DX quotientSGK //; first by rewrite subsetI; case/andP.
by rewrite normal_norm // (normalS _ _ NMP) //; case/andP: SXP.
Qed.

(* Gorenstein 5.3.11 *)
Lemma pgroup_crit: forall P, p_group P ->
  {C: {group gT} | [/\ C \char P,
                       (nil_class C <= 2 /\ abelem (C/'Z(C))),
                       [~: P , C] \subset 'Z(C) &
                       'C_P(C) = 'Z(C)]}.
Proof.
move=> P PgP; pose f (x: {set gT}) := (x \char P) && abelian x.
case: (@maxgroup_exists _ f 1); rewrite /f {f}; first by rewrite trivg_char abelian1.
move=> {f}D; case/maxgroupP; case/andP => ChD AD MD _.
pose f (x: {set gT}) := [&& (x <| P), abelian x & D \subset x].
case: (@maxgroup_exists _ f D); rewrite /f {f}.
  by rewrite (char_normal ChD) AD subxx.
move=> M HM; case/maxgroupP: (HM); case/and3P => NMP AM SDM MM _.
case ChM: (M \char P); move/idP: ChM => ChM.
  have AC: 'Z(M) = M by apply/setIidPl; case/maxgroupP: HM; case/andP.
  exists M; split=> //; last first.
  - rewrite AC; apply: (crit_lem) => //.
    apply/maxgroupP; split; first by rewrite NMP.
    move=> H; case/andP=> NHP AH SMH.
    by apply: MM => //; rewrite NHP AH (subset_trans SDM).
  - by rewrite AC commg_subr; case/andP: (char_normal ChM).
  split.
    rewrite /nil_class;case: #|M| => [|[|n]] //=; case: (_ == 1) => //.
    by rewrite ucn_lcnP ucn1 AC eqxx.
  by rewrite AC trivg_quotient abelem1.
pose P' := (P / D)%G; pose H := 'C_P(D)%G; pose H' := (H / D :&: P')%G.
pose C' := (H' :&: 'Ohm_1('Z(P')))%G.
pose C := (coset_morphism D @*^-1 C')%G.
exists C.
have ECC': C' :=: C / D by rewrite /= cosetpreK.
move: SDM; rewrite subEproper; case/orP => PDM.
  by case: ChM; rewrite -(eqP PDM).
have PDH: D \proper H.
  by rewrite (proper_sub_trans PDM) // subsetI (normal_sub NMP)
             centsC (subset_trans (proper_sub PDM)).
have ChH: H \char P := subcent_char (char_refl _) ChD.
have nTH: H' :!=: 1.
  rewrite -subG1 /= -quotientIG // ?(char_sub ChD) // quotient_sub1 //.
    apply: proper_subn.
    by rewrite (proper_sub_trans PDH) // !(subsetI, subIset) ?subxx ?orbT.
  by rewrite setIC subIset // char_norm.
pose K := (coset_morphism D @*^-1 'Ohm_1('Z(P')))%G.
have EKOZP': 'Ohm_1('Z(P')) = K / D by rewrite /= cosetpreK.
have ChK: K \char P.
  apply: (char_from_quotient _ ChD); first by rewrite normal_cosetpre.
  by rewrite cosetpreK; apply: char_trans (center_char _); exact: Ohm_char.
have CE: C :=: H :&: K.
  rewrite /= !morphpreI /= !quotientGK //=; last exact: char_normal.
    by congr (_ :&: _); rewrite setIAC setIid.
  apply: (normalS _ _ (char_normal ChD)); first exact: (proper_sub PDH).
  exact: (char_sub ChH).
have ChC: C \char P by rewrite CE; apply: charI.
have SD'ZC: D \subset 'Z(C).
  by rewrite subsetI {1}/C /C' /H' /P' /H sub_cosetpre centsC CE setIAC subsetIr.
have EZCD: 'Z(C) :=: D.
  rewrite /C /C' /H' /H /P'; apply: MD => //.
  apply/andP=> //; split; first by apply: (char_trans (center_char _)).
  by rewrite /abelian subIset // centsC subsetIr.
have F1: [~: P, C] \subset 'Z(C).
  rewrite EZCD /= -quotient_cents2 //=.
  - by rewrite cosetpreK centsC (subset_trans (subsetIr _ _)) //
               (subset_trans (@Ohm_sub 1 _ _)) // subsetIr.
  - exact: char_norm ChD.
  by rewrite cents_norm // centsC -{1}EZCD subsetIr.
split => //.
  - split; last first.
      by rewrite EZCD cosetpreK /= (abelemS (subsetIr _ _)) //
        Ohm_abelian // ?abelian_center // (@pgroup_p _ (pdiv #|P|)) //
                (@pgroupS _ _ (P/D)) // (center_sub,  morphim_pgroup).
   rewrite /nil_class; case: #|C| => [|[|[|n]]] //=;
     case: (_ == _) => //; case: (_ == _) => //.
   suff->: 'L_2(C) == 1 by done.
   rewrite (@ucn_lcnP _ C) ucnSnR ucn1 /=.
   rewrite eqEsubset; apply/andP; split; apply/subsetP=> x; rewrite in_set.
       by case/andP.
   move=> IxC; rewrite IxC; apply: subset_trans F1.
   apply/subsetP=> z; case/imsetP=> y IyC->; rewrite  mem_commg //.
   by apply: (subsetP (char_sub ChC)).
apply/eqP; rewrite eqEsubset.
rewrite {2}/center setSI ?andbT ?(char_sub ChC) //.
suff SCCC: 'C_P(C) \subset C.
  by rewrite /center subsetI SCCC subsetIr.
set Q := 'C_P(C)%G.
case E1: (Q \subset C); move/idPn: E1 => E1 //.
have QICD: Q :&: C = D.
  rewrite -EZCD /center /Q -setIA setIC -(setIA 'C(C)).
  suff->: C :&: P = C by rewrite setIC.
  by apply/setIidPl; apply: char_sub.
have QIH: Q \subset H by rewrite setIS // centS // -QICD subsetIr.
have NDQ: D <| Q.
  apply: normalS (char_normal ChD); last by rewrite subsetIl.
  by rewrite -QICD; rewrite subsetIl.
pose Q' := (Q / D)%G.
have Q'IH': Q' \subset H'.
  rewrite subsetI quotientSGK ?(proper_sub PDH) //; last by case/andP: NDQ.
  rewrite QIH quotientSGK //; last by apply: (char_sub ChD).
    by rewrite (subset_trans QIH) // (char_sub ChH) //.
  by case/andP: NDQ.
have TQ'C': Q' :&: C' = 1.
  rewrite ECC'.
  suff<-: (Q :&: C) / D = Q' :&: C / D by rewrite QICD trivg_quotient.
  by   apply: quotientIG; rewrite -{1}QICD subsetIr.
have NQ'P': Q' <| P'.
  apply: morphim_normal.
  rewrite /normal subIset ?subxx; last by done.
  apply/normsP=> p IpP; rewrite /H conjIg conjGid -?centJ; last by done.
  have: C <| P by apply: char_normal.
  by case/andP => _; move/normsP; move/(_ _ IpP) => ->.
have TQ': Q' :!=: 1.
  rewrite -subG1 quotient_sub1 -QICD.
  apply: contra E1 => TDQ'.
  apply: (subset_trans TDQ'); first by rewrite subsetIr.
  by rewrite QICD; case/andP: NDQ.
have NTQ'ZP': Q' :&: 'Z(P') != 1.
  apply: contra TQ'; move/eqP; move/nil_TI_Z=> -> //.
  by apply: quotient_nil; apply: (pgroup_nil PgP).
have NTQ'OZP': Q' :&: 'Ohm_1('Z(P')) != 1.
  by apply: contra NTQ'ZP'; move/eqP; move/TI_Ohm1->.
case/negP: NTQ'OZP'; rewrite -subG1 -TQ'C'.
rewrite subsetI subsetIl subsetI subsetIr andbT.
by apply: (subset_trans _  Q'IH'); rewrite subsetIl.
Qed.


End CriticalThompson.

