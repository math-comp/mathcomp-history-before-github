(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic commutator nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxrepresentation vector.
Require Import BGsection1 BGsection3 BGsection7 BGsection10.
Require Import BGsection14 BGsection15 BGsection16.
Require Import algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 8: Structure of a Minimal Simple      *)
(* Group of Odd Order. Actually, most Section 8 definitions can be found in   *)
(* BGsection16, which holds the conclusions of the Local Analysis part of the *)
(* proof, as the B & G text has been adapted to fit the usage in Section 8.   *)
(* Most of the definitions of Peterfalvi Section 8 are covered in BGsection7, *)
(* BGsection15 and BGsection16; we only give here:                            *)
(*   FT_Pstructure W W1 W2 S T <-> the groups W, W1, W2, S, and T satisfy the *)
(*                    conclusion of Theorem (8.8)(b), in particular,          *)
(*                    W = W1 \x W2, S = S^(1) ><| W1, T = T^`(1) ><| W2, and  *)
(*                    both S and T are of type P.                             *)
(*           'R[x] == the "signalizer" group of x \in 'A1(M) for the Dade     *)
(*                    hypothesis of M (note: this is only extensionally equal *)
(*                    to the 'R[x] defined in BGsection14).                   *)
(*            'R_M == the signalizer functor for the Dade hypothesis of M.    *)
(*                    Note that this only maps x to 'R[x] for x in 'A1(M).    *)
(*                    The casual use of the R(x) in Peterfalvi is improper,   *)
(*                    as its meaning depends on which maximal group is        *)
(*                    considered.                                             *)
(*         'A1~(M) == the support of the image of the restricted Dade         *)
(*                    isometry on M (when M is maximal).                      *)
(*          'A~(M) == the support of the image of the Dade isometry on M.     *)
(*         'A0~(M) == the support of the image of the externded Dade isometry *)
(*                    on M (this definition is not used).                     *)
(*  FTsupports M L <-> L supports M in the sense of (8.14) and (8.18). This   *)
(*                    definition is not used outside this file.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.

Local Open Scope ring_scope.

(* Supercedes the notation in BGsection14. *)
Notation "''R' [ x ]" := 'C_((gval 'N[x])`_\F)[x]
 (at level 8, format "''R' [ x ]")  : group_scope.
Notation "''R' [ x ]" := 'C_('N[x]`_\F)[x]%G : Group_scope.

Section Definitions.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types L M X : {set gT}.

(* These cover Peterfalvi, Definition (8.14). *)
Definition FTsignalizer M x := if 'C[x] \subset M then 1%G else 'R[x]%G.

Definition FTsupports M L :=
   existsb x, [&& x \in 'A(M), ~~ ('C[x] \subset M) & 'C[x] \subset L].

Definition FT_Dade_support M X :=
  \bigcup_(x \in X) class_support (FTsignalizer M x :* x) G.

End Definitions.

Notation "''R_' M" := (FTsignalizer M)
 (at level 8, M at level 2, format "''R_' M") : group_scope.

Notation "''A1~' ( M )" := (FT_Dade_support M 'A1(M))
  (at level 8, format "''A1~' ( M )").

Notation "''A~' ( M )" := (FT_Dade_support M 'A(M))
  (at level 8, format "''A~' ( M )").

Notation "''A0~' ( M )" := (FT_Dade_support M 'A0(M))
  (at level 8, format "''A0~' ( M )").

Section Eight.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L M N P Q R S T U V W : {group gT}.

(* Peterfalvi, Definition (8.1) is covered by BGsection16.of_typeF. *)

(* This is the remark following Definition (8.1). *)
Remark compl_of_typeF M U V (H := M`_\F) :
  H ><| U = M -> of_typeF M V -> of_typeF M U.
Proof.
move=> defM_U [[]]; rewrite -/H => ntH ntV defM part_b part_c.
have oU: #|U| = #|V|.
  apply/eqP; rewrite -(@eqn_pmul2l #|H|) ?cardG_gt0 //.
  by rewrite (sdprod_card defM) (sdprod_card defM_U).
have [x Mx defU]: exists2 x, x \in M & U :=: V :^ x.
  pose pi := \pi(V); have hallV: pi.-Hall(M) V.
    by rewrite Hall_pi // -(sdprod_Hall defM) (pHall_Hall (Fcore_Hall M)).
  apply: Hall_trans (hallV).
    rewrite mFT_sol // (sub_proper_trans _ (mFT_norm_proper ntH _)) ?gFnorm //.
    rewrite (proper_sub_trans _ (subsetT M)) // properEcard gFsub.
    by rewrite -(sdprod_card defM) ltn_Pmulr ?cardG_gt0 ?cardG_gt1.
  rewrite pHallE -(card_Hall hallV) oU eqxx andbT.
  by case/sdprod_context: defM_U.
have nHx: x \in 'N(H) by apply: subsetP Mx; rewrite gFnorm.
split; first by rewrite {1}defU conjsg_eq1.
  have [U1 [nsU1U abU1 prU1H]] := part_b.
  rewrite defU; exists (U1 :^ x)%G; split; rewrite ?normalJ ?abelianJ //.
  rewrite -/H -(normP nHx) -conjD1g => _ /imsetP[h Hh ->].
  by rewrite -conjg_set1 normJ -conjIg conjSg prU1H.
have [U0 [sU0V expU0 frobHU0]] := part_c.
have [defHU0 _ ntU0 _ _] := Frobenius_context frobHU0.
rewrite defU; exists (U0 :^ x)%G; split; rewrite ?conjSg ?exponentJ //.
by rewrite -/H -(normP nHx) -conjYg FrobeniusJ.
Qed.

Lemma Frobenius_of_typeF M U (H := M`_\F) :
  [Frobenius M = H ><| U] -> of_typeF M U.
Proof.
move=> frobM; have [defM ntH ntU _ _] := Frobenius_context frobM.
have [_ _ nHU tiHU] := sdprodP defM.
split=> //; last by exists U; split; rewrite // -sdprodEY ?defM.
exists 1%G; split; rewrite ?normal1 ?abelian1 //.
by move=> x /(Frobenius_reg_compl frobM)->.
Qed.

(* This is Peterfalvi (8.2).                                                  *)
Lemma typeF_context M U (H := M`_\F) :
    of_typeF M U ->
  [/\ (*a*) forall U0, is_typeF_complement M U U0 -> #|U0| = exponent U,
      (*b*) [Frobenius M = H ><| U] = Zgroup U
    & (*c*) forall U1 (i : Iirr H),
            is_typeF_inertia M U U1 -> i != 0 -> 'I_U['chi_i] \subset U1].
Proof.
case; rewrite -/H => [[ntH ntM defM] _ exU0]; set part_a := forall U0, _.
have [nsHM sUG mulHU nHU _] := sdprod_context defM.
have oU0: part_a.
  move=> U0 [sU0U <- /Frobenius_reg_ker regU0]; rewrite exponent_Zgroup //.
  apply/forall_inP=> S /SylowP[p _ /and3P[sSU0 pS _]].
  apply: odd_regular_pgroup_cyclic pS (mFT_odd S) ntH _ _.
    by rewrite (subset_trans (subset_trans sSU0 sU0U)).
  by move=> x /setD1P[ntx /(subsetP sSU0) U0x]; rewrite regU0 // !inE ntx.
split=> // [|U1 i [nsU1U abU1 s_cUH_U1] nz_i].
  apply/idP/idP=> [frobU | ZgU].
    apply/forall_inP=> S /SylowP[p _ /and3P[sSU pS _]].
    apply: odd_regular_pgroup_cyclic pS (mFT_odd S) ntH _ _.
      by rewrite (subset_trans sSU).
    move=> x /setD1P[ntx /(subsetP sSU) Ux].
    by rewrite (Frobenius_reg_ker frobU) // !inE ntx.
  have [U0 [sU0U expU0 frobU0]] := exU0; have regU0 := Frobenius_reg_ker frobU0.
  suffices defU0: U0 :=: U by rewrite defU0 norm_joinEr ?mulHU // in frobU0.
  by apply/eqP; rewrite eqEcard sU0U /= (oU0 U0) // exponent_Zgroup.
have itoP: is_action M (fun (j : Iirr H) x => conjg_Iirr j x).
  split=> [x | j x y Mx My].
    apply: can_inj (fun j => conjg_Iirr j x^-1) _ => j.
    by apply: chi_inj; rewrite !conjg_IirrE cfConjgK.
  by apply: chi_inj; rewrite !conjg_IirrE (cfConjgM _ nsHM).
pose ito := Action itoP; pose cto := ('Js \ subsetT M)%act.
have actsMcH: [acts M, on classes H | cto].
  apply/subsetP=> x Mx; rewrite !inE Mx; apply/subsetP=> _ /imsetP[y Hy ->].
  have nHx: x \in 'N(H) by rewrite (subsetP (gFnorm _ _)).
  rewrite !inE /= -class_rcoset norm_rlcoset // class_lcoset mem_classes //.
  by rewrite memJ_norm.
apply/subsetP=> g /setIdP[/setIP[Ug nHg] c_i_g]; have Mg := subsetP sUG g Ug.
apply: contraR nz_i => notU1g; rewrite (sameP eqP set1P).
suffices <-: 'Fix_ito[g] = [set (0 : Iirr H)].
  by rewrite !inE sub1set inE -(inj_eq (@chi_inj _ _)) conjg_IirrE.
apply/eqP; rewrite eq_sym eqEcard cards1 !(inE, sub1set) /=.
rewrite -(inj_eq (@chi_inj _ _)) conjg_IirrE chi0_1 cfConjg_cfun1 eqxx.
rewrite (card_afix_irr_classes Mg actsMcH) => [|j y z Hy /=]; last first.
  case/imsetP=> _ /imsetP[t Ht ->] -> {z}.
  by rewrite conjg_IirrE cfConjgE // conjgK cfunJ.
rewrite -(cards1 [1 gT]) subset_leq_card //= -/H.
apply/subsetP=> _ /setIP[/imsetP[a Ha ->] /afix1P caHg]; rewrite inE classG_eq1.
have{caHg} /imsetP[x Hgx cax]: a \in a ^: (H :* g).
  by rewrite class_rcoset caHg class_refl.
have coHg: coprime #|H| #[g].
  apply: (coprime_dvdr (order_dvdG Ug)).
  by rewrite (coprime_sdprod_Hall defM) (pHall_Hall (Fcore_Hall M)).
have /imset2P[z y cHgg_z Hy defx]: x \in class_support ('C_H[g] :* g) H.
  have [/and3P[/eqP defUcHgg _ _] _] := partition_cent_rcoset nHg coHg.
  by rewrite class_supportEr -cover_imset defUcHgg.
rewrite -(can_eq (conjgKV y)) conj1g; apply: contraR notU1g => nt_ay'.
have{nt_ay'} Hay': a ^ y^-1 \in H^# by rewrite !inE nt_ay' groupJ ?groupV.
rewrite (subsetP (s_cUH_U1 _ Hay')) // inE Ug.
have ->: g = z.`_(\pi(H)^').
  have [h /setIP[Hh /cent1P cgh] ->] := rcosetP cHgg_z.
  rewrite consttM // (constt1P _) ?mul1g ?constt_p_elt //.
    by rewrite /p_elt -coprime_pi' ?cardG_gt0.
  by rewrite (mem_p_elt _ Hh) // pgroupNK pgroup_pi.
by rewrite groupX //= -conjg_set1 normJ mem_conjgV -defx !inE conjg_set1 -cax.
Qed.

(* Peterfalvi, Definition (8.3) is covered by BGsection16.of_typeI. *)
(* Peterfalvi, Definition (8.4) is covered by BGsection16.of_typeP. *)

(* These correspond to the remarks following Definition (8.4). *)
Remark of_typeP_sol M U W1 : of_typeP M U W1 -> solvable M.
Proof.
case=> _ [nilU _ _ defM'] _ _ _.
have [nsHM' _ mulHU _ _] := sdprod_context defM'.
rewrite (series_sol (der_normal 1 M)) (abelian_sol (der_abelian 0 M)) andbT.
rewrite (series_sol nsHM') (nilpotent_sol (Fcore_nil M)).
by rewrite -mulHU quotientMidl quotient_sol ?(nilpotent_sol nilU).
Qed.

Remark of_typeP_compl_conj M W1 V K (M' := M^`(1)%g) :
  M' ><| W1 = M -> of_typeP M V K -> gval W1 \in K :^: M.
Proof.
move=> defM typeM_P; have solM := of_typeP_sol typeM_P.
have [[_ /Hall_pi hallK _ defM_K] _ _ _ _] := typeM_P.
apply/imsetP; apply: Hall_trans solM _ (hallK).
rewrite pHallE; have [_ -> _ _ _] := sdprod_context defM.
rewrite /= -(card_Hall hallK) -(@eqn_pmul2l #|M'|) ?cardG_gt0 //.
by rewrite (sdprod_card defM) (sdprod_card defM_K).
Qed.

Lemma FTtypePF_exclusion M U1 U W1 : ~ (of_typeF M U1 /\ of_typeP M U W1).
Proof.
move=> [[[ntH ntU1 defM1] _ [U0 [sU01 expU0] frobU0]] typeP_M].
have [[cycW1 hallW1 ntW1 defM] [_ _ _ defM'] _ [_]] := typeP_M; case/negP.
pose p := pdiv #|W1|; set H := M`_\F in defM' frobU0 *.
have piW1p: p \in \pi(W1) by rewrite pi_pdiv cardG_gt1.
have piU0p: p \in \pi(U0).
  rewrite -pi_of_exponent expU0 pi_of_exponent (pi_of_dvd _ _ piW1p) //=.
  rewrite -(@dvdn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defM1).
  rewrite -(sdprod_card defM) dvdn_pmul2r ?cardSg //.
  by case/sdprodP: defM' => _ <- _ _; exact: mulG_subl.
have [|X EpX]:= @p_rank_geP _ p 1 U0 _; first by rewrite p_rank_gt0.
have [ntX [sXU0 abelX _]] := (nt_pnElem EpX isT, pnElemP EpX).
have piW1_X: \pi(W1).-group X by apply: pi_pgroup piW1p; case/andP: abelX.
have sXM: X \subset M.
  apply: subset_trans (subset_trans sXU0 sU01) _.
  by case/sdprodP: defM1 => _ <- _ _; exact: mulG_subr.
have nHM: M \subset 'N(H) by exact: gFnorm.
have [regU0 solM] := (Frobenius_reg_ker frobU0, of_typeP_sol typeP_M).
have [a Ma sXaW1] := Hall_Jsub solM (Hall_pi hallW1) sXM piW1_X.
rewrite -subG1 -(conjs1g a) -(cent_semiregular regU0 sXU0 ntX) conjIg -centJ.
by rewrite (normsP nHM) ?setIS ?centS.
Qed.

Remark typeP_witness M :
    M \in 'M -> FTtype M != 1%N ->
  exists U : {group gT}, exists W1 : {group gT}, of_typeP M U W1.
Proof.
move=> maxM /negbTE typeMnot1.
have:= FTtype_range M; rewrite -mem_iota !inE typeMnot1 /=.
case/or4P; case/FTtypeP=> //; try by move=> U [W1 [[?]]]; exists U, W1.
by move=> W1 [? _]; exists 1%G, W1.
Qed.

Remark compl_of_typeP M W1 (M' :=  M^`(1)%g) (H := M`_\F) :
    M' ><| W1 = M -> M \in 'M -> FTtype M != 1%N ->
  exists U : {group gT}, of_typeP M U W1.
Proof.
move=> defM maxM /typeP_witness[// | U [K typeM_P]].
have /imsetP[x Mx ->] := of_typeP_compl_conj defM typeM_P.
have [nM'x nHx] : x \in 'N(M') /\ x \in 'N(H).
  by rewrite !(subsetP _ x Mx) ?gFnorm.
have [PMa PMb PMc PMd PMe] := typeM_P; exists (U :^ x)%G; split=> //.
- rewrite cyclicJ HallJ //= conjsg_eq1 -/M' -(normP nM'x) -sdprodJ.
  by have [-> -> -> ->] := PMa; rewrite conjGid.
- rewrite /= -/M' -/H -(normP nM'x) -(normP nHx) -sdprodJ normJ !conjSg.
  rewrite -{1}(setTI U) -morphim_conj injm_nil ?subsetT ?injm_conj //.
  by have [-> -> -> ->] := PMb.
- rewrite /= -/H -/M' -(normP nHx) -(normP nM'x) -(normsP (der_norm 2 M) x Mx).
  rewrite centJ -conjD1g -conjIg cyclicJ conjsg_eq1 !conjSg.
  have [-> -> -> -> prKM'] := PMd; split=> // _ /imsetP[y Ky ->].
  by rewrite cent1J -conjIg prKM'.
rewrite /= -/H -(normP nHx) centJ -conjIg -conjYg -conjUg -conjDg => X.
rewrite -(can_eq (conjsgKV x)) conj0g -sub_conjgV => ? /PMe <- //.
by rewrite normJ conjsgKV.
Qed.

(* A much weaker version of this, conjugating only U, might suffice. *)
Remark of_typeP_conj M U W1 V K :
    of_typeP M U W1 -> of_typeP M V K ->
  exists x, [/\ x \in M, U :=: V :^ x & W1 :=: K :^ x].
Proof.
case=> [[_ _ _ defM] [_ _ nUW1 defM'] _ _ _] typeM_P; set H := M`_\F in defM'.
set M' := M^`(1)%g in defM defM'.
have{defM} /imsetP[y My defW1] := of_typeP_compl_conj defM typeM_P.
have /andP[sM'M nM'M]: M' <| M by exact: der_normal.
have solM': solvable M' := solvableS sM'M (of_typeP_sol typeM_P).
have [[_ hallK _ defM] [_ _ nVK defM'_V] _ _ _] := typeM_P.
have [_ /mulG_sub[sHM' sUM'] _ _] := sdprodP defM'.
have hallV: \pi(V).-Hall(M') V.
  rewrite Hall_pi // -(sdprod_Hall defM'_V).
  exact: pHall_Hall (pHall_subl _ _ (Fcore_Hall M)).
have hallU: \pi(V).-Hall(M') (U :^ y^-1%g).
  rewrite pHallE sub_conjgV (normsP nM'M) ?sUM' //= cardJg. 
  rewrite -(card_Hall hallV) -(@eqn_pmul2l #|H|) ?cardG_gt0 //.
  by rewrite (sdprod_card defM'_V) (sdprod_card defM').
have coM'K: coprime #|M'| #|K|.
  by rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM).
have [_ _ nM'K _] := sdprodP defM.
have [|z] := coprime_Hall_trans nM'K coM'K solM' hallU _ hallV nVK.
  by rewrite normJ -sub_conjg -defW1.
case/setIP=> /(subsetP sM'M) Mz cKz defVz; exists (z * y)%g.
by rewrite groupM // !conjsgM -defVz conjsgKV (normsP (cent_sub K) z cKz).
Qed.

(* This is Peterfalvi (8.5), with an extra clause in anticipation of (8.15). *)
Lemma typeP_context M U W1 (H := M`_\F) (W2 := 'C_H(W1)) (W := W1 <*> W2) :
    of_typeP M U W1 ->
  [/\ (*a*) H \x 'C_U(H) = 'F(M),
      (*b*) U^`(1)%g \subset 'C(H) /\ (U :!=: 1%g -> ~~ (U \subset 'C(H))),
      (*c*) normedTI (W :\: (W1 :|: W2)) G W
    & cyclicTIhypothesis G W W1 W2].
Proof.
case; rewrite /= -/H -/W2 -/W => [] [cycW1 hallW1 ntW1 defM] [nilU _ _ defM'].
set V := W :\: _ => [] [_ sM''F defF sFM'] [cycW2 ntW2 _ _ _] TI_V.
have [/andP[sHM' nHM'] sUM' mulHU _ tiHU] := sdprod_context defM'.
have sM'M : M^`(1)%g \subset M by exact: der_sub.
have hallH_M' := pHall_subl sHM' sM'M (Fcore_Hall M).
have{defF} defF: (H * 'C_U(H))%g = 'F(M).
  rewrite -(setIidPl sFM') -defF -group_modl //= -/H.
  rewrite setIAC (setIidPr (der_sub 1 M)).
  rewrite -(coprime_mulG_setI_norm mulHU) ?norms_cent //; last first.
    by rewrite (coprime_sdprod_Hall defM') (pHall_Hall hallH_M').
  by rewrite mulgA (mulGSid (subsetIl _ _)).
have coW12: coprime #|W1| #|W2|.
  rewrite coprime_sym (coprimeSg (subset_trans (subsetIl H _) sHM')) //.
  by rewrite (coprime_sdprod_Hall defM) (sdprod_Hall defM).
have defW: (W1 * W2 = W)%g by rewrite -cent_joinEr ?subsetIr.
have oV: #|V| = (#|W1|.-1 * #|W2|.-1)%N.
  rewrite -!subn1 muln_subr muln1 muln_subl mul1n -coprime_cardMg // defW.
  rewrite subn_sub addn_subA // addnC -cardsUI coprime_TIg // cards1 addnK.
  by rewrite cardsD (setIidPr _) // subUset -join_subG.
have cycW: cyclic W by rewrite cyclicY ?subsetIr.
have tiVW: normedTI V G W.
  have cWW: abelian W := cyclic_abelian cycW.
  have cWV: V \subset 'C(W) by rewrite (centSS _ _ cWW) ?subsetDl.
  have neqV0: V != set0.
    by rewrite -cards_eq0 -lt0n oV -!subn1 muln_gt0 !subn_gt0 !cardG_gt1 ntW1.
  apply/normedTI_P; rewrite // setTI cents_norm 1?centsC //.
  split=> // g _ /pred0Pn[v /andP[/= Vv Vgv]]; rewrite -/W.
  have nWg: g \in 'N(W).
    rewrite inE -{2}(TI_V [set v]) ?sub1set //.
      by rewrite sub_cent1 centJ (subsetP _ v Vgv) // conjSg.
    by apply: contraTneq (set11 v) => ->; rewrite inE.
  have [chW1 chW2]: W1 \char W /\ W2 \char W.
    by apply/andP; rewrite !sub_cyclic_char -?join_subG.
  by rewrite -(TI_V V) ?(subsetP _ g nWg) ?normsD // normsU ?char_norms.
split=> //; first by rewrite dprodE ?subsetIr //= setIA tiHU setI1g.
  split.
    apply: subset_trans (_ : U :&: 'F(M) \subset _).
      by rewrite subsetI der_sub (subset_trans (dergS 1 sUM')).
    by rewrite -defF -group_modr ?subsetIl // setIC tiHU mul1g subsetIr.
  apply: contra => cHU; rewrite -subG1 -tiHU subsetIidr (subset_trans sUM') //.
  have hallM': \pi(M^`(1)%g).-Hall(M) M^`(1)%g.
    by rewrite Hall_pi // (sdprod_Hall defM).
  by rewrite (Fcore_max hallM') ?der_normal // -mulHU mulg_nil ?Fcore_nil.
by split; rewrite // mFT_odd subsetT dprodE ?subsetIr ?coprime_TIg.
Qed.

(* Peterfalvi, Definition (8.6) is covered by BGsection16.of_typeII_IV et al. *)

Remark compl_of_typeII_IV M U W1 :
  of_typeP M U W1 -> M \in 'M -> FTtype M != 5 -> of_typeII_IV M U W1.
Proof.
move=> typeM_P naxM typeMnot5.
have [V [K typeVK]]: exists V, exists K, of_typeII_IV M (gval V) (gval K).
  have:= FTtype_range M; rewrite -mem_iota !inE (negbTE typeMnot5) orbF.
  case/or4P; case/FTtypeP=> //; try by move=> V [K []]; exists V, K.
  by move=> K [typeM_F _]; case: (@FTtypePF_exclusion M K U W1).
have [typeM_P_VK ntV prK tiF] := typeVK.
have [x [Mx defU defW1]] := of_typeP_conj typeM_P typeM_P_VK.
by split; rewrite // (defW1, defU) (cardJg, conjsg_eq1).
Qed.

Remark compl_of_typeII M U W1 (H := M`_\F) (M' := M^`(1)%g) :
  of_typeP M U W1 -> M \in 'M -> FTtype M == 2 -> of_typeII M U W1.
Proof.
move=> typeM_P maxM typeM.
have [V [K [[typeVK _ _ _]]]] := FTtypeP 2 maxM typeM.
have [x [Mx -> _]] := of_typeP_conj typeVK typeM_P; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg => cUU not_s_nUM typeM' defH.
split=> //; first by apply: compl_of_typeII_IV; rewrite // (eqP typeM).
by apply: compl_of_typeF typeM'; rewrite defH; have [_ []] := typeM_P.
Qed.

Remark compl_of_typeIII M U W1 (H := M`_\F) (M' := M^`(1)%g) :
  of_typeP M U W1 -> M \in 'M -> FTtype M == 3 -> of_typeIII M U W1.
Proof.
move=> typeM_P maxM typeM.
have [V [K [[typeVK _ _ _]]]] := FTtypeP 3 maxM typeM.
have [x [Mx -> _]] := of_typeP_conj typeVK typeM_P; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg.
by split=> //; apply: compl_of_typeII_IV; rewrite // (eqP typeM).
Qed.

Remark compl_of_typeIV M U W1 (H := M`_\F) (M' := M^`(1)%g) :
  of_typeP M U W1 -> M \in 'M -> FTtype M == 4 -> of_typeIV M U W1.
Proof.
move=> typeM_P maxM typeM.
have [V [K [[typeVK _ _ _]]]] := FTtypeP 4 maxM typeM.
have [x [Mx -> _]] := of_typeP_conj typeVK typeM_P; rewrite -/M' -/H.
rewrite abelianJ normJ -{1}(conjGid Mx) conjSg.
by split=> //; apply: compl_of_typeII_IV; rewrite // (eqP typeM).
Qed.

(* Peterfalvi, Definition (8.7) is covered by BGsection16.of_typeV. *)

Remark compl_of_typeV M U W1 (H := M`_\F) (M' := M^`(1)%g) :
  of_typeP M U W1 -> M \in 'M -> FTtype M == 5 -> U = 1%G /\ of_typeV M W1.
Proof.
move=> typeM_P maxM typeM; have [K [type1K]] := FTtypeP 5 maxM typeM.
have [x [Mx defU ->]] := of_typeP_conj type1K typeM_P; rewrite cardJg.
have U1: U = 1%G.
  by apply: (act_inj 'JG x); apply: val_inj; rewrite /= -defU conjs1g.
by do 2?split=> //; rewrite -(congr_group U1).
Qed.

Definition all_typeI := forallb M, (M \in 'M) ==> (@FTtype gT M == 1%N).

(* This is the statement of Peterfalvi, Theorem (8.8)(b). *)
Definition FT_Pstructure W W1 W2 S T :=
 [/\       [/\ cyclicTIhypothesis G W W1 W2, S \in 'M & T \in 'M],
    (*b1*) [/\ S^`(1) ><| W1 = S, T^`(1) ><| W2 = T & S :&: T = W]%g,
    (*b2*) FTtype S == 2 \/ FTtype T == 2,
    (*b3*) (1 < FTtype S <= 5 /\ 1 < FTtype T <= 5)%N
  & (*b4*) {in 'M, forall M,
             FTtype M != 1%N -> exists x, M :=: S :^ x \/ M :=: T :^ x}].

Lemma FT_Pstructure_sym W W1 W2 S T :
  FT_Pstructure W W1 W2 S T -> FT_Pstructure W W2 W1 T S.
Proof.
case=> [] [/cyclicTIhyp_sym ? ? ?] [? ?]; rewrite setIC => ? b3 [? ?] b5.
split=> //; first by case: b3; [right | left].
by move=> _ _ /=/b5[// | x [] ->]; exists x; [right | left].
Qed.

Inductive some_FT_Pstructure : Prop :=
   Some_FT_Pstructure W W1 W2 S T of FT_Pstructure W W1 W2 S T.

(* This is Peterfalvi, Theorem (8.8). *)
Lemma FT_FPstructure : 
  if all_typeI then (*a*) {in 'M, forall M, FTtype M == 1%N}
               else (*b*) some_FT_Pstructure.
Proof.
case: all_typeI / forall_inP => // not_allF.
have [_ [// | [[S T] [[maxS maxT] [[W1 W2] /=]]]]] := BGsummaryI gT.
set W := W1 <*> W2; set V := W :\: _ => [[[cycW tiV nVW _ [ntW1 ntW2]]]].
move=> b1 b4 b2 b3; exists [group of W] W1 W2 S T; split => //; last first.
  by move=> _ _ /=/b4 [// | x [] <-]; exists x; [left | right].
have{b1 b3 b4} [defS defT _] := b1; split=> //.
have coW12: coprime #|W1| #|W2|.
  have{ntW1 ntW2 nVW tiV} ntV: V != set0.
    apply: contraTneq (cyclic_abelian cycW); rewrite -nVW => ->.
    by rewrite -(setDv 1%g) normD1 norm1 mFT_nonAbelian.
  rewrite {}/V {}/W in cycW ntV.
  without loss{b2 defT maxT} typeS: S T W1 W2 maxS defS cycW ntV / FTtype S = 2.
    move=> IH; case: b2 cycW ntV => /eqP/IH; first exact.
    by rewrite coprime_sym joingC setUC; exact.
  have{maxS typeS defS} prW1: prime #|W1|.
    have [|U typeS_P] := compl_of_typeP defS maxS; first by rewrite typeS.
    by have [|//] := compl_of_typeII_IV typeS_P maxS; rewrite typeS.
  rewrite prime_coprime // (cardSg_cyclic cycW) ?joing_subl ?joing_subr //.
  by apply: contra ntV => sW12; rewrite (joing_idPr sW12) (setUidPr sW12) setDv.
split=> //; last by rewrite /normedTI tiV nVW setTI /=.
rewrite mFT_odd subsetT dprodEY ?coprime_TIg //.
by rewrite (sub_abelian_cent2 (cyclic_abelian cycW)) ?joing_subl ?joing_subr.
Qed.

(* This is Peterfalvi (8.9). *)
Lemma def_cycTIcompl W W1 W2 S T :
  FT_Pstructure W W1 W2 S T -> 'C_(S`_\F)(W1) = W2.
Proof.
case=> [[cycW maxS _] [defS _ defST] _ [typeS _] _].
have coW12 := (cyclicTI_coprime cycW).
have{cycW} [[/dprodP[_ defW cW12 _] _ _ _] [ntW1 _ ] /andP[_ nVW]] := cycW.
have{typeS}: FTtype S != 1%N by apply: contraTneq typeS => ->.
case/(compl_of_typeP defS maxS)=> U []; set S' := S^`(1)%g; set K := 'C_(_)(W1).
case=> cycW1 /Hall_pi hallW1 _ /sdprodP[_ _ _ tiS'W1] _ _ [cycK _ _ _ defK] _.
have [x defW1] := cyclicP cycW1.
have{defK ntW1} defK: K = 'C_S'[x].
  by rewrite defK // !inE -cycle_subG -cycle_eq1 -defW1 subxx ntW1.
have sW2S': W2 \subset S'.
  have nsS'S: S' <| S := der_normal 1 S.
  have hallS': \pi(W1)^'.-Hall(S) S' by exact/(sdprod_normal_pHallP _ hallW1).
  rewrite (sub_normal_Hall hallS' nsS'S); first by rewrite coprime_pi' in coW12.
  by apply: subset_trans (subsetIl S T); rewrite defST -defW mulG_subr.
have sW2K: W2 \subset K by rewrite defK -cent_cycle -defW1 subsetI sW2S' cW12.
have defW2: W2 :=: S' :&: W by rewrite -defW -group_modr // tiS'W1 mul1g.
apply/eqP; rewrite eqEsubset sW2K defW2 subsetI {1}defK subsetIl -(eqP nVW) /=.
have abW1K: abelian (W1 <*> K) by rewrite abelianY ?cyclic_abelian ?subsetIr.
rewrite setTI cents_norm // (sub_abelian_cent2 abW1K) ?joing_subr //.
by rewrite subDset setUC subsetU // -defW -genM_join sub_gen ?mulgS.
Qed.

Lemma FT_cycTI_hyp M U W1 (W2 := 'C_(M`_\F)(W1)%G) (W := (W1 <*> W2)%G) :
   of_typeP M U W1 -> cyclicTIhypothesis [set: gT] W W1 W2.
Proof. by case/typeP_context. Qed.

Section OneMaximal.

Variable M : {group gT}.
Hypothesis maxM : M \in 'M.

(* Peterfalvi, Definition (8.10) is covered in BGsection16. *)

(* This is Peterfalvi (8.11). *)
Lemma FTcore_facts :
 [/\ Hall G M`_\F, Hall G M`_\s
   & forall S, Sylow M`_\s S -> S :!=: 1%g -> 'N(S) \subset M].
Proof.
have hallMs := Msigma_Hall_G maxM; have [_ sMs _] := and3P hallMs.
rewrite def_FTcore // (pHall_Hall hallMs).
split=> // [|S /SylowP[p _ sylS] ntS].
  have sMF_Ms:= Fcore_sub_Msigma maxM.
  apply: (@pHall_Hall _ \pi(M`_\F)); apply: (subHall_Hall hallMs).
    by move=> p /(piSg sMF_Ms)/(pnatPpi sMs).
  exact: pHall_subl (pcore_sub _ M) (Fcore_Hall M).
have s_p: p \in \sigma(M).
  by rewrite (pnatPpi sMs) // -p_rank_gt0 -(rank_Sylow sylS) rank_gt0.
by apply: (norm_sigma_Sylow s_p); exact: (subHall_Sylow (Msigma_Hall maxM)).
Qed.

(* This is Peterfalvi (8.12). *)
(* (b) could be stated for subgroups of U wlog -- usage should be checked.   *)
Lemma FTtypeI_II_facts n U (H := M`_\F) :
    FTtype M == n -> H ><| U = M ^`(n.-1)%g ->
  if 0 < n <= 2 then
  [/\ (*a*) forall p S, p.-Sylow(U) S -> abelian S /\ ('r(S) <= 2)%N,
      (*b*) forall X, X != set0 -> X \subset U^# -> 'C_H(X) != 1%g ->
            'M('C(X)) = [set M]
    & (*c*) let A := 'A(M) :\: 'A1(M) in trivIset (A :^: G) /\ M \subset 'N(A)
  ] else True.
Proof.
move=> typeM defMn; have [n12 | //] := ifP; rewrite -mem_iota !inE in n12.
have defH: H = M`_\sigma.
  by rewrite -def_FTcore -?(Fcore_eq_FTcore _ _) // (eqP typeM) !inE orbA n12.
have [K complU]: exists K : {group gT}, kappa_complement M U K.
  have [[V K] /= complV] := kappa_witness maxM.
  have [[hallV hallK gVK] [_ sUMn _ _ _]] := (complV, sdprod_context defMn).
  have hallU: \sigma_kappa(M)^'.-Hall(M) U.
    rewrite pHallE -(card_Hall hallV) (subset_trans sUMn) ?der_sub //=.
    rewrite -(@eqn_pmul2l #|H|) ?cardG_gt0 // (sdprod_card defMn) defH.
    rewrite (sdprod_card (sdprod_FTder maxM complV)) (eqP typeM).
    by case/pred2P: n12 => ->.
  have [x Mx defU] := Hall_trans (mmax_sol maxM) hallU hallV.
  exists (K :^ x)%G; split; rewrite ?pHallJ // defU -conjsMg.
  by rewrite -(gen_set_id gVK) groupP.
have [part_a _ _ [part_b part_c]] := BGsummaryB maxM complU.
split=> // X notX0 /subsetD1P[sXU notX1]; rewrite -cent_gen defH.
apply: part_b; rewrite -?subG1 ?gen_subG //.
by rewrite  -setD_eq0 setDE (setIidPl _) // subsetC sub1set inE.
Qed.

(* This is Peterfalvi (8.13). *)
(* We have substituted the B & G notation for the unique maximal supergroup   *)
(* of 'C[x], and specialized the lemma to X := 'A0(M).                        *)
Lemma FTsupport_facts (X := 'A0(M)) (D := [set x \in X | ~~('C[x] \subset M)]) :
  [/\ (*a*) {in X &, forall x, {subset x ^: G <= x ^: M}},
      (*b*) D \subset 'A1(M) /\ {in D, forall x, 'M('C[x]) = [set 'N[x]]}
    & (*c*) {in D, forall x (L := 'N[x]) (H := L`_\F),
        [/\ (*c1*) H ><| (M :&: L) = L /\ 'C_H[x] ><| 'C_M[x] = 'C[x],
            (*c2*) {in X, forall y, coprime #|H| #|'C_M[y]| },
            (*c3*) x \in 'A(L) :\: 'A1(L)
          & (*c4*) 1 <= FTtype L <= 2
                /\ (FTtype L == 2 -> [Frobenius M with kernel M`_\F])]}].
Proof.
have defX: X \in pred2 'A(M) 'A0(M) by rewrite !inE eqxx orbT.
have [sDA1 part_a part_c] := BGsummaryII maxM defX.
have{part_a} part_a: {in X &, forall x, {subset x ^: G <= x ^: M}}.
  move=> x y A0x A0y /= /imsetP[g Gg def_y]; rewrite def_y.
  by apply/imsetP/part_a; rewrite -?def_y.
do [split=> //; first split=> //] => x /part_c[_ []] //.
rewrite -(mem_iota 1) !inE => -> [-> ? -> -> L2_frob].
by do 2![split=> //] => /L2_frob[U /FrobeniusWker].
Qed.

(* A generic proof of the first assertion of Peterfalvi (8.15). *)
Let norm_FTsuppX A :
  M \subset 'N(A) -> 'A1(M) \subset A -> A \subset 'A0(M) -> 'N(A) = M.
Proof.
move=> nAM sA1A sAA0; apply: mmax_max => //.
rewrite (sub_proper_trans (norm_gen _)) ?mFT_norm_proper //; last first.
  rewrite (sub_proper_trans _ (mmax_proper maxM)) // gen_subG.
  by rewrite (subset_trans sAA0) // (subset_trans (FTsupp0_sub M)) ?subsetDl.
rewrite (subG1_contra (genS sA1A)) //= genD1 ?group1 //.
by rewrite genGid /= def_FTcore ?Msigma_neq1.
Qed.

Lemma norm_FTsupp1 : 'N('A1(M)) = M.
Proof. exact: norm_FTsuppX (FTsupp1_norm M) _ (FTsupp1_sub0 maxM). Qed.

Lemma norm_FTsupp : 'N('A(M)) = M.
Proof. exact: norm_FTsuppX (FTsupp_norm M) (FTsupp1_sub _) (FTsupp_sub M). Qed.

Lemma norm_FTsupp0 : 'N('A0(M)) = M.
Proof. exact: norm_FTsuppX (FTsupp0_norm M) (FTsupp1_sub0 _) _. Qed.

Lemma FTsignalizerJ x y : 'R_(M :^ x) (y ^ x) :=: 'R_M y :^ x.
Proof.
rewrite /'R__ /= {1}cent1J conjSg; case: ifP => _ /=; first by rewrite conjs1g.
by rewrite cent1J FT_signalizer_baseJ FcoreJ -conjIg.
Qed.

Let is_FTsignalizer : is_Dade_signalizer G M 'A0(M) 'R_M.
Proof.
rewrite /'R_M => x A0x /=; rewrite setTI.
case: ifPn => [sCxM | not_sCxM]; first by rewrite sdprod1g (setIidPr sCxM).
by have [_ _ /(_ x)[| [] //]] := FTsupport_facts; exact/setIdP.
Qed.

(* This is Peterfalvi (8.15), second assertion. *)
Lemma FT_Dade0_hyp : Dade_hypothesis G M 'A0(M).
Proof.
have [part_a _ parts_bc] := FTsupport_facts.
have /subsetD1P[sA0M notA0_1] := FTsupp0_sub M.
split; rewrite // /normal ?sA0M ?norm_FTsupp0 //=.
exists 'R_M => [|x y A0x A0y]; first exact: is_FTsignalizer.
rewrite /'R_M; case: ifPn => [_ | not_sCxM]; first by rewrite cards1 coprime1n.
rewrite (coprimeSg (subsetIl _ _)) //=.
by have [| _ -> //] := parts_bc x; exact/setIdP.
Qed.

Lemma def_FTsignalizer : {in 'A0(M), Dade_signalizer FT_Dade0_hyp =1 'R_M}.
Proof. exact: def_Dade_signalizer. Qed.

Definition FT_Dade_hyp :=
  restr_Dade_hyp FT_Dade0_hyp (FTsupp_sub M) (FTsupp_norm M).

Definition FT_Dade1_hyp :=
  restr_Dade_hyp FT_Dade0_hyp (FTsupp1_sub0 maxM) (FTsupp1_norm M).

Lemma FT_Dade1_supportE : Dade_support FT_Dade1_hyp = 'A1~(M).
Proof.
rewrite restr_Dade_support; apply: eq_bigr => x A1x.
by rewrite /Dade_support1 def_FTsignalizer // (subsetP (FTsupp1_sub0 maxM)).
Qed.

Lemma FT_Dade_supportE : Dade_support FT_Dade_hyp = 'A~(M).
Proof.
rewrite restr_Dade_support; apply: eq_bigr => x Ax.
by rewrite /Dade_support1 def_FTsignalizer // inE Ax.
Qed.

Lemma FT_Dade1_supportJ x : 'A1~(M :^ x) = 'A1~(M).
Proof.
rewrite /'A1~(_) FTsupp1J big_imset /=; last exact: in2W (conjg_inj x).
apply: eq_bigr => y _; rewrite FTsignalizerJ -conjg_set1 -conjsMg.
rewrite !class_supportEl big_imset /=; last exact: in2W (conjg_inj x).
by apply: eq_bigr => z _; rewrite -class_lcoset lcoset_id ?inE.
Qed.

Lemma FT_Dade_supportJ x : 'A~(M :^ x) = 'A~(M).
Proof.
rewrite /'A~(_) FTsuppJ big_imset /=; last exact: in2W (conjg_inj x).
apply: eq_bigr => y _; rewrite FTsignalizerJ -conjg_set1 -conjsMg.
rewrite !class_supportEl big_imset /=; last exact: in2W (conjg_inj x).
by apply: eq_bigr => z _; rewrite -class_lcoset lcoset_id ?inE.
Qed.

(* Need more Section 3/4/5 material to complete the formalization of (8.15). *)

(* This is Peterfalvi (8.16). *)
Lemma FTtypeII_ker_TI :
   FTtype M == 2 ->
 [/\ normedTI 'A0(M) G M, normedTI 'A(M) G M & normedTI 'A1(M) G M].
Proof.
move=> typeM; have [sA1A sAA0] := (FTsupp1_sub maxM, FTsupp_sub M).
have [sA10 sA0M] := (subset_trans sA1A sAA0, FTsupp0_sub M).
have nzA1: 'A1(M) != set0 by rewrite setD_eq0 def_FTcore ?subG1 ?Msigma_neq1.
have [nzA nzA0] := (subset_neq0 sA1A nzA1, subset_neq0 sA10 nzA1).
suffices nTI_A0: normedTI 'A0(M) G M.
  by rewrite nTI_A0 !(normedTI_S _ _ _ nTI_A0) // ?FTsupp_norm ?FTsupp1_norm.
have sA0G1: 'A0(M) \subset G^# by exact: subset_trans (setSD _ (subsetT M)).  
have [U [W1 [[typeM_P _ _ tiFM] _ _ _ _]]] := FTtypeP 2 maxM typeM.
apply/Dade_normedTI_P=> //; exists FT_Dade0_hyp => x A0x.
rewrite /= def_FTsignalizer /'R_M //=; have [// | not_sCxM] := ifPn.
have [y cxy /negP[]] := subsetPn not_sCxM.
have /setD1P[ntx Ms_x]: x \in 'A1(M).
  by have [_ [/subsetP-> // ]] := FTsupport_facts; exact/setIdP.
have Fx: x \in 'F(M)^#.
  rewrite !inE ntx (subsetP (Fcore_sub_Fitting M)) //.
  by rewrite (Fcore_eq_FTcore _ _) ?(eqP typeM).
rewrite -(mmax_normal maxM (Fitting_normal M)) //; last first.
  by rewrite -subG1 -setD_eq0; apply/set0Pn; exists x.
rewrite -normD1 (sameP normP eqP); apply: wlog_neg => /(trivIsetP tiFM).
rewrite  mem_orbit ?orbit_refl // => /(_ isT isT) /pred0Pn[].
by exists x; rewrite /= mem_conjg /conjg mulgA invgK (cent1P cxy) mulgK Fx.
Qed.

End OneMaximal.

(* This is Peterfalvi, Theorem (8.17). *)
Theorem FT_Dade_support_partition :
  [/\ (*a1*) \pi(G) =i [pred p | existsb M : {group gT},
                                 (M \in 'M) && (p \in \pi(M`_\s))],
      (*a2*) {in 'M &, forall M L,
                gval L \notin M :^: G -> coprime #|M`_\s| #|L`_\s| },
      (*b*) {in 'M, forall M, #|'A1~(M)| = (#|M`_\s|.-1 * #|G : M|)%N}
    & (*c*) let PG := [set 'A1~(gval Mi) | Mi <- 'M^G] in
       [/\ {in 'M^G &, injective (fun M => 'A1~(M))},
           all_typeI -> partition PG G^#
         & forall W W1 W2 S T (VG := class_support (W :\: (W1 :|: W2)) G),
             FT_Pstructure W W1 W2 S T ->
           partition (VG |: PG) G^# /\ VG \notin PG]].
Proof.
have defDsup M: M \in 'M -> class_support M^~~ G = 'A1~(M).
  move=> maxM; rewrite class_supportEr /'A1~(M) /'A1(M) def_FTcore //.
  rewrite -(eq_bigr _ (fun _ _ => bigcupJ _ _ _ _)) exchange_big /=.
  apply: eq_bigr => x Ms_x; rewrite -class_supportEr.
  rewrite -norm_rlcoset ?(subsetP (cent_sub _)) ?cent_FT_signalizer //=.
  congr (class_support (_ :* x) G); rewrite /'R_M.
  have [_ _ /(_ x Ms_x)[_ defCx _] /(_ x Ms_x)defNF]:= BGsummaryD maxM.
  have [sCxM | /defNF[[_ <-]] //] := ifPn.
  apply/eqP; rewrite trivg_card1 -(eqn_pmul2r (cardG_gt0 'C_M[x])).
  by rewrite (sdprod_card defCx) mul1n /= (setIidPr _).
have [b [a1 a2] [/and3P[_ _ not_PG_set0] _ _]] := BGsummaryE gT.
split=> [p | M L maxM maxL /a2 | M maxM | {b a1 a2}PG].
- apply/idP/exists_inP=> [/a1[M maxM sMp] | [M _]].
    by exists M => //; rewrite def_FTcore // pi_Msigma.
  exact: piSg (subsetT _) p.
- move/(_ maxM maxL)=> coML; rewrite coprime_pi' // !def_FTcore //.
  apply: sub_pgroup (pcore_pgroup _ L) => p; apply/implyP.
  by rewrite implybN /= pi_Msigma // implybE -negb_and [_ && _]coML.
- by rewrite -defDsup // def_FTcore // b.
have [/subsetP sMG_M _ injMG sM_MG] := mmax_transversalP gT.
have{PG} ->: PG = [set class_support (gval M)^~~ G | M <- 'M].
  apply/setP=> AG; apply/imsetP/imsetP=> [] [M maxM ->].
    by move/sMG_M in maxM; exists M; rewrite ?defDsup //.
  have [x MG_Mx] := sM_MG M maxM.
  by exists (M :^ x)%G; rewrite // defDsup ?mmaxJ ?FT_Dade1_supportJ.
have [c1 c2] := mFT_partition gT.
split=> [M H maxM maxH eq_MH | strG_F | W W1 W2 S T VG strG_P].
- apply: injMG => //; move/sMG_M in maxM; move/sMG_M in maxH.
  apply/orbit_transl/idPn => not_HG_M.
  have /negP[]: ~~ [disjoint 'A1~(M) & 'A1~(H)].
   rewrite eq_MH -setI_eq0 setIid -defDsup //.
   by apply: contraNneq not_PG_set0 => <-; exact: mem_imset.
  rewrite -!defDsup // -setI_eq0 class_supportEr big_distrl -subset0.
  apply/bigcupsP=> x /class_supportGidr <- /=; rewrite -conjIg sub_conjg conj0g.
  rewrite class_supportEr big_distrr /=; apply/bigcupsP=> {x}x _.
  rewrite subset0 setI_eq0 -sigma_supportJ sigma_support_disjoint ?mmaxJ //.
  by rewrite (orbit_transr _ (mem_orbit _ _ _)) ?in_setT // orbit_sym.
- rewrite c1 // setD_eq0; apply/subsetP=> M maxM.
  by rewrite FTtype_Fmax ?(forall_inP strG_F).
have [[cycW maxS _] [defS _ _] _ [/andP[typeS _] _] _] := strG_P.
rewrite ltn_neqAle eq_sym in typeS; case/andP: typeS => typeS _.
have maxP_S: S \in TypeP_maxgroups _ by rewrite FTtype_Pmax.
have [U typeP_S] := compl_of_typeP defS maxS typeS.
have hallW1: \kappa(S).-Hall(S) W1.
  have [[U1 K] /= complU1] := kappa_witness maxS.
  have ntK: K :!=: 1%g by rewrite -(trivgPmax maxS complU1).
  have [[defS_K _ _] [//|defS' _] _ _ _] := kappa_structure maxS complU1.
  rewrite {}defS' in defS_K.
  have /imsetP[x Sx defK] := of_typeP_compl_conj defS_K typeP_S.
  by have [_ hallK _] := complU1; rewrite defK pHallJ in hallK.
have{cycW} [[/dprodP[_ defW cW12 _] cycW _ _] [ntW1 ntW2 ] _] := cycW.
have defW2: 'C_(S`_\sigma)(W1) = W2.
  have [U1 complU1] := ex_kappa_compl maxS hallW1.
  have [[_ [_ _ sW2'F] _] _ _ _] := BGsummaryC maxS complU1 ntW1.
  rewrite -(setIidPr sW2'F) setIA (setIidPl (Fcore_sub_Msigma maxS)).
  exact: def_cycTIcompl strG_P.
by have [] := c2 _ _ maxP_S hallW1; rewrite defW2 /= cent_joinEr // defW -/VG.
Qed.

(* This is Peterfalvi (8.18). Note that only part (c) is actually used later. *)
Lemma FT_Dade_support_disjoint S T :
    S \in 'M -> T \in 'M -> gval T \notin S :^: G ->
  [/\ (*a*) FTsupports S T = ~~ [disjoint 'A1(S) & 'A(T)]
         /\ {in 'A1(S) :&: 'A(T), forall x,
               ~~ ('C[x] \subset S) /\ 'C[x] \subset T},
      (*b*) (existsb x, FTsupports S (T :^ x)) = ~~ [disjoint 'A1~(S) & 'A~(T)]
    & (*c*) [disjoint 'A1~(S) & 'A~(T)] \/  [disjoint 'A1~(T) & 'A~(S)]].
Proof.
move: S T; pose NC S T := gval T \notin S :^: G.
have part_a2 S T (maxS : S \in 'M) (maxT : T \in 'M) (ncST : NC S T) :
  {in 'A1(S) :&: 'A(T), forall x, ~~ ('C[x] \subset S) /\ 'C[x] \subset T}.
- move=> x /setIP[/setD1P[ntx Ss_x] ATx].
  have coxTs: coprime #[x] #|T`_\s|.
    apply: (coprime_dvdl (order_dvdG Ss_x)).
    by have [_ ->] := FT_Dade_support_partition.
  have [z /setD1P[ntz Ts_z] /setD1P[_ /setIP[Tn_x czx]]] := bigcupP ATx.
  set n := FTtype T != 1%N in Tn_x.
  have typeT: FTtype T == n.+1.
    have notTs_x: x \notin T`_\s.
      apply: contra ntx => Ts_x.
      by rewrite -order_eq1 -dvdn1 -(eqnP coxTs) dvdn_gcd dvdnn order_dvdG.
    apply: contraLR ATx => typeT; rewrite FTsupp_eq1 // ?inE ?ntx //.
    move: (FTtype_range T) typeT; rewrite -mem_iota /n.
    by do 5!case/predU1P=> [-> // | ].
  have defTs: T`_\s = T`_\F.
    by apply/esym/Fcore_eq_FTcore; rewrite // (eqP typeT); case n.
  have [U Ux defTn]: exists2 U : {group gT}, x \in U & T`_\F ><| U = T^`(n)%g.
    have [[U K] /= complU] := kappa_witness maxT.
    have defTn: T`_\s ><| U = T^`(n)%g.
      by rewrite def_FTcore // (sdprod_FTder maxT complU).
    have nsTsTn: T`_\s <| T^`(n)%g by case/sdprod_context: defTn.
    have [sTsTn nTsTn] := andP nsTsTn.
    have hallTs: \pi(T`_\s).-Hall(T^`(n)%g) T`_\s.
      by rewrite defTs (pHall_subl _ (der_sub n T) (Fcore_Hall T)) //= -defTs.
    have hallU: \pi(T`_\s)^'.-Hall(T^`(n)%g) U.
      by apply/sdprod_Hall_pcoreP; rewrite /= (normal_Hall_pcore hallTs).
    have solTn: solvable T^`(n)%g := solvableS (der_sub n T) (mmax_sol maxT).
    rewrite coprime_sym coprime_pi' // in coxTs.
    have [|y Tn_y] := Hall_subJ solTn hallU _ coxTs; rewrite cycle_subG //.
    exists (U :^ y)%G; rewrite // -defTs.
    by rewrite -(normsP nTsTn y Tn_y) -sdprodJ defTn conjGid.
  have uniqCx: 'M('C[x]) = [set T].
    have:= FTtypeI_II_facts maxT typeT defTn; rewrite !ltnS leq_b1 -cent_set1.
    case=> _ -> //; first by rewrite -cards_eq0 cards1.
      by rewrite sub1set !inE ntx.
    by apply/trivgPn; exists z; rewrite //= -defTs inE Ts_z cent_set1 cent1C.
  split; last by case/mem_uniq_mmax: uniqCx.
  by apply: contra ncST => /(eq_uniq_mmax uniqCx maxS)->; exact: orbit_refl.
have part_a1 S T (maxS : S \in 'M) (maxT : T \in 'M) (ncST : NC S T) :
  FTsupports S T = ~~ [disjoint 'A1(S) & 'A(T)].
- apply/existsP/pred0Pn=> [[x /and3P[ASx not_sCxS sCxT]] | [x /andP[A1Sx Atx]]].
    have [_ [/subsetP]] := FTsupport_facts maxS; set D := finset _.
    have Dx: x \in D by rewrite !inE ASx.
    move=> /(_ x Dx) A1x /(_ x Dx)uniqCx /(_ x Dx)[_ _ /setDP[ATx _] _].
    by rewrite (eq_uniq_mmax uniqCx maxT sCxT); exists x; exact/andP.
  exists x; rewrite (subsetP (FTsupp1_sub maxS)) //=.
  by apply/andP/part_a2=> //; exact/setIP.
have part_b S T (maxS : S \in 'M) (maxT : T \in 'M) (ncST : NC S T) :
  (existsb x, FTsupports S (T :^ x)) = ~~ [disjoint 'A1~(S) & 'A~(T)].
- apply/existsP/pred0Pn=> [[x] | [y /andP[/= A1GSy AGTy]]].
    rewrite part_a1 ?mmaxJ // => [/pred0Pn[y /andP/=[A1Sy ATyx]]|]; last first.
      by rewrite /NC -(rcoset_id (in_setT x)) orbit_rcoset.
    rewrite FTsuppJ mem_conjg in ATyx; exists (y ^ x^-1); apply/andP; split.
      by apply/bigcupP; exists y => //; rewrite mem_imset2 ?rcoset_refl ?inE.
    apply/bigcupP; exists (y ^ x^-1) => //.
    by rewrite (subsetP (sub_class_support _ _)) ?rcoset_refl.
  have{AGTy} [x2 ATx2 x2R_yG] := bigcupP AGTy.
  have [sCx2T | not_sCx2T] := boolP ('C[x2] \subset T); last first.
    have [_ _ _ [injA1G pGI pGP]] := FT_Dade_support_partition.
    have{pGI pGP} tiA1g: trivIset [set 'A1~(gval M) | M <- 'M^G].
      case: ifP FT_FPstructure => [/pGI/and3P[] // | _ [W W1 W2 S' T' /pGP[]]].
      by case/and3P=> _ /(trivIsetS (subsetUr _ _)).
    have [_ _ injMG sM_MG] := mmax_transversalP gT.
    have [_ [sDA1T _] _] := FTsupport_facts maxT.
    have [[z1 maxSz] [z2 maxTz]] := (sM_MG S maxS, sM_MG T maxT).
    case/imsetP: ncST; exists (z1 * z2^-1)%g; first by rewrite inE.
    rewrite conjsgM; apply/(canRL (conjsgK _))/congr_group/injA1G=> //.
    apply/eqP/idPn=> /(trivIsetP tiA1g)/pred0Pn[]; try exact: mem_imset.
    exists y; rewrite !FT_Dade1_supportJ /= A1GSy andbT.
    by apply/bigcupP; exists x2; rewrite // (subsetP sDA1T) ?inE ?ATx2.
  have{x2R_yG} /imsetP[z _ def_y]: y \in x2 ^: G.
    by rewrite /'R_T {}sCx2T mul1g class_support_set1l in x2R_yG.
  have{A1GSy} [x1 A1Sx1] := bigcupP A1GSy; rewrite {y}def_y -mem_conjgV.
  rewrite class_supportGidr ?inE {z}//.
  case/imset2P=> _ z /rcosetP[y Hy ->] _ def_x2.
  exists z^-1%g; rewrite part_a1 ?mmaxJ //; last first.
    by rewrite /NC (orbit_transr _ (mem_orbit _ _ _)) ?inE.
  apply/pred0Pn; exists x1; rewrite /= A1Sx1 FTsuppJ mem_conjgV; apply/bigcupP.
  pose ddS := FT_Dade1_hyp maxS; have [/andP[sA1S _] _ notA1_1 _ _] := ddS.
  have [ntx1 Sx1] := (memPn notA1_1 _ A1Sx1, subsetP sA1S _ A1Sx1).
  have [coHS defCx1] := (Dade_coprime ddS A1Sx1 A1Sx1, Dade_sdprod ddS A1Sx1).
  rewrite (restr_Dade_signalizer _ _ (def_FTsignalizer maxS)) // in coHS defCx1.
  have[u Ts_u /setD1P[_ cT'ux2]] := bigcupP ATx2.
  exists u => {Ts_u}//; rewrite 2!inE -(conj1g z) (can_eq (conjgK z)) ntx1.
  suffices{u cT'ux2} ->: x1 = (y * x1).`_(\pi('R_S x1)^').
    by rewrite -consttJ -def_x2 groupX.
  have /setIP[_ /cent1P cx1y]: y \in 'C_G[x1].
    by case/sdprod_context: defCx1 => /andP[/subsetP->].
  rewrite consttM // (constt1P _) ?p_eltNK ?(mem_p_elt (pgroup_pi _)) // mul1g.
  have piR'_Cx1: \pi('R_S x1)^'.-group 'C_S[x1] by rewrite coprime_pi' in coHS.
  by rewrite constt_p_elt ?(mem_p_elt piR'_Cx1) // inE Sx1 cent1id.
move=> S T maxS maxT ncST; split; first split; auto.
apply/orP/idPn; rewrite negb_or -part_b // => /andP[suppST /negP[]].
without loss{suppST} suppST: T maxT ncST / FTsupports S T.
  move=> IH; case/existsP: suppST => x /IH {IH}.
  rewrite FT_Dade1_supportJ (orbit_transr _ (mem_orbit _ _ _)) ?in_setT //.
  by rewrite mmaxJ => ->.
have{suppST} [y /and3P[ASy not_sCyS sCyT]] := existsP suppST.
have Dy: y \in [set z \in 'A0(S) | ~~ ('C[z] \subset S)] by rewrite !inE ASy.
have [_ [_ /(_ y Dy) uCy]  /(_ y Dy)[_ coTcS _ typeT]] := FTsupport_facts maxS.
rewrite  -mem_iota -(eq_uniq_mmax uCy maxT sCyT) !inE in coTcS typeT.
apply/negbNE; rewrite -part_b /NC 1?orbit_sym // negb_exists.
apply/forallP=> x; rewrite part_a1 ?mmaxJ ?negbK //; last first.
  by rewrite /NC (orbit_transr _ (mem_orbit _ _ _)) ?in_setT // orbit_sym.
rewrite -setI_eq0 -subset0 FTsuppJ -bigcupJ big_distrr; apply/bigcupsP=> z Sxz.
rewrite conjD1g /= -setDIl coprime_TIg ?setDv //= cardJg.
rewrite -(Fcore_eq_FTcore maxT _) ?inE ?orbA; last by have [->] := typeT.
by rewrite (coprimegS _ (coTcS z _)) ?(subsetP (FTsupp1_sub0 _)) ?setSI ?gFsub.
Qed.

End Eight.

Notation FT_Dade0 maxM := (Dade (FT_Dade0_hyp maxM)).
Notation FT_Dade maxM := (Dade (FT_Dade_hyp maxM)).

