(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxpoly mxrepresentation mxabelem vector.
Require Import falgebra fieldext finfield.
Require Import BGsection1 BGsection2 BGsection3 BGsection7.
Require Import BGsection15 BGsection16.
Require Import ssrnum ssrint algC classfun character inertia vcharacter.
Require Import PFsection1 PFsection2 PFsection3 PFsection4 PFsection5.
Require Import PFsection6 PFsection7 PFsection8 PFsection9 PFsection11.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma flattenP (T : eqType) (A : seq (seq T)) x :
  reflect (exists2 s, s \in A & x \in s) (x \in flatten A).
Proof.
elim: A => /= [|s A /iffP IH_A]; [by right; case | rewrite mem_cat].
have [s_x|s'x] := @idP (x \in s); first by left; exists s; rewrite ?mem_head.
by apply: IH_A => [[t] | [t /predU1P[->|]]]; exists t; rewrite // mem_behead.
Qed.
Implicit Arguments flattenP [T A x].

Lemma flatten_mapP (aT rT : eqType) (A : aT -> seq rT) s y :
  reflect (exists2 x, x \in s & y \in A x) (y \in flatten (map A s)).
Proof.
apply: (iffP flattenP) => [[_ /mapP[x sx ->]] | [x sx]] Axy; first by exists x.
by exists (A x); rewrite ?map_f.
Qed.
Implicit Arguments flatten_mapP [aT rT A s y].

Lemma flatten_imageP (aT : finType) (rT : eqType) A (P : pred aT) (y : rT) :
  reflect (exists2 x, x \in P & y \in A x) (y \in flatten [seq A x | x in P]).
Proof.
by apply: (iffP flatten_mapP) => [][x Px]; exists x; rewrite ?mem_enum in Px *.
Qed.
Implicit Arguments flatten_imageP [aT rT A P y].

Import GroupScope GRing.Theory FinRing.Theory Num.Theory.
Local Open Scope ring_scope.

Lemma irr_constt_ortho (gT : finGroupType) (G : {group gT})
                       (phi psi : 'CF(G)) i j : 
    phi \is a character -> psi \is a character ->
    i \in irr_constt phi -> j \in irr_constt psi ->
  '[phi, psi] = 0 -> '['chi_i, 'chi_j] = 0.
Proof.
move=> _ _ /constt_charP[//|phi1 Nphi1 ->] /constt_charP[//|psi1 Npsi1 ->].
rewrite cfdot_irr; case: eqP => // -> /eqP/idPn[].
rewrite cfdotDl !cfdotDr cfnorm_irr -addrA gtr_eqF ?ltr_paddr ?ltr01 //.
by rewrite Cnat_ge0 ?rpredD ?Cnat_cfdot_char ?irr_char.
Qed.

Section PFTwelve.

Variable gT : minSimpleOddGroupType.
Local Notation G := (TheMinSimpleOddGroup gT).
Implicit Types (p q : nat) (x y z : gT).
Implicit Types H K L M N P Q R S T U V W : {group gT}.

Section Twelve2.

(* Hypothesis 12.1 *)
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
(* Local Notation H' := H^`(1)%G. *)
(* Local Notation "` 'H''" := `H^`(1) (at level 0) : group_scope. *)

(* This is wrong : we define here 
{\theta \in Irr (L) | H \in ker \theta and 1%g is not included in ker \theta 
otherwise said the empty set.
Local Notation calS := (Iirr_kerD L 1%g H).*)

(* use Let instead of Local Notation to avoid unused occurrences of H *)
Let calS := seqIndD H L H 1%G.

(* there is hidden occurrences of L here so let's use let *)
Let tau := FT_Dade maxL.

(* Remark : if the objet you're defining is equipped with some *)
(* canonical structure, the CS can be infered under a let but the definition *)
(* is expanded and you'll have to fold it back by hand after inference *)
(* took place. A local notation might be a better option *)

Let S_ (chi : 'CF(L)) := [set i in irr_constt chi].

Let calI := [seq 'chi_i | i in Iirr_kerD L H 1%G].

Lemma chi_calI i : i \in Iirr_kerD L H 1%g -> 'chi_i \in calI.
Proof. by move=> i_Iirr; apply/imageP; exists i. Qed.

Lemma S_calSP i : 
  reflect (exists2 chi, chi \in calS & i \in S_ chi) (i \in Iirr_kerD L H 1%G).
Proof.
have nHL : H <| L by exact: gFnormal.
have sHL : H \subset L by apply: normal_sub.
apply: (iffP idP) => [| hiU].
  case: (constt_cfRes_irr H i) => t; rewrite -constt_Ind_constt_Res => hi hker.
  suff ? : 'Ind[L]'chi_t \in calS by exists ('Ind[L] 'chi_t); rewrite // inE.
  apply/seqIndC1P; exists t => //.
  rewrite -(subGcfker t) (sub_cfker_constt_Ind_irr hi) ?normal_norm //.
  by move: hker; rewrite !inE; case/andP.
rewrite /Iirr_kerD;  rewrite !inE sub1G andbT; move: hiU.
case=> k kcalS; rewrite inE; case/seqIndC1P: (kcalS) => t kert ->.
move/sub_cfker_constt_Ind_irr/(_ (subxx _)) => <- //; last exact: normal_norm.
by rewrite subGcfker.
Qed.

(* This is Peterfalvi (12.2a), first part *)
Lemma PF_12_2a chi : chi \in calS ->
  [/\ chi = \sum_(i in S_ chi) 'chi_i,
      constant [seq 'chi_i 1%g | i in S_ chi] &
      {in S_ chi, forall i, 'chi_i \in 'CF(L, 1%g |: 'A(L))}].
Proof.
move=> calS_chi; case/seqIndC1P: (calS_chi) => t kert Dchi.
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
have defT: H ><| 'I_U['chi_t] = T := sdprod_modl sdHU (sub_inertia 'chi_t).
have abTbar : abelian (T / H).
  have [_ _ /(_ _ _ inertU1 kert) sItU1] := (typeF_context Utype).
  have [nU1U abU1 _] := inertU1.
  rewrite /T; have /sdprodP [_ <- _ _] := defT.
  by rewrite quotientMidl quotient_abelian // (abelianS sItU1).
have Dchi_sum : chi = \sum_(i in S_ chi) 'chi_i.
  rewrite {1}Dchi; have /= [-> _ _] := induced_inertia_quo1 nHL abTbar copHIchi.
  by rewrite Dchi (eq_bigl _ _ (in_set _)) (reindex_constt_inertia _ _ id).
have lichi : constant [seq 'chi_i 1%g | i in S_ chi].
  have /= [_ _ Ichi1] := induced_inertia_quo1 nHL abTbar copHIchi.
  pose c := #|L : T|%:R * 'chi_t 1%g; apply: (@all_pred1_constant _ c).
  apply/allP=> _ /imageP[s tLs ->] /=.
  rewrite inE Dchi -Ind_Iirr_constt_inertia // in tLs.
  by have{s tLs} /imsetP[s tTs ->] := tLs; rewrite inertia_Ind_IirrE ?Ichi1.
suffices CF_S : {in S_ chi, forall i, 'chi_i \in 'CF(L, 1%g |: 'A(L))} by [].
move=> j Schi_j /=; apply/cfun_onP => y A'y.
have [Ly | /cfun0->//] := boolP (y \in L).
have CHy1: 'C_H[y] = 1%g.
  apply: contraNeq A'y => /trivgPn[z /setIP[Hz cyz] ntz].
  rewrite !inE -implyNb; apply/implyP=> nty; apply/bigcupP.
  rewrite /'A1(L) /L`_\s (eqP Ltype) /=; exists z; first by rewrite !inE ntz.
  by rewrite 3!inE nty Ly cent1C.
have: j \in Iirr_kerD L H 1%G by apply/S_calSP; exists chi.
by rewrite !inE => /andP[/not_in_ker_char0->].
Qed.

(* This is Peterfalvi (12.2a), second part *)
Lemma tau_isometry : {in 'Z[calI, L^#], isometry tau, to 'Z[irr G, G^#]}.
Proof.
apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
rewrite zcharD1E => /andP[S_phi phi1_0].
have /subsetD1P[_ /setU1K <-] := FTsupp_sub L; rewrite zcharD1 {}phi1_0 andbT.
apply: zchar_trans_on phi S_phi => _ /imageP[i /S_calSP[j calSj Sj_i] ->].
by rewrite zchar_split irr_vchar; have [_ _ ->] := PF_12_2a calSj.
Qed.

Lemma cc_calI : conjC_closed calI.
Proof.
move=> _ /imageP[i Ii ->]; rewrite !inE in Ii; apply/imageP.
by exists (conjC_Iirr i); rewrite ?inE conjC_IirrE ?cfker_aut.
Qed.

Lemma FPtype1_irr_subcoherent : 
  {R : 'CF(L) -> seq 'CF(G) | subcoherent calI tau R}.
Proof.
apply: irr_subcoherent; last exact: tau_isometry.
  have UcalI: uniq calI by apply/dinjectiveP; apply: in2W irr_inj.
  by split=> // [_ /mapP[i _ ->]|]; [apply: mem_irr | apply: cc_calI].
apply/hasPn=> psi; case/imageP => i; rewrite !inE => /andP[kerH'i _] ->.
rewrite /cfReal odd_eq_conj_irr1 ?mFT_odd // irr_eq1 -subGcfker.
by apply: contra kerH'i; apply: subset_trans; apply: gFsub.
Qed.
Local Notation R1gen := FPtype1_irr_subcoherent.

(* This is Peterfalvi (12.2)(b). *)
Lemma FPtype1_subcoherent (R1 := sval R1gen) :
  {R : 'CF(L) -> seq 'CF(G) |
    [/\ subcoherent calS tau R,
        {in Iirr_kerD L H 1%G, forall i (phi := 'chi_i),
         [/\ orthonormal (R1 phi),
             size (R1 phi) = 2
           & tau (phi - phi^*%CF) = \sum_(mu <- R1 phi) mu]}
    & forall chi, R chi = flatten [seq R1 'chi_i | i in S_ chi]]}.
Proof.
have nHL : H <| L by exact: gFnormal.
have nrS : ~~ has cfReal calS by apply: seqInd_notReal; rewrite ?mFT_odd.
have U_S : uniq calS by exact: seqInd_uniq.
have ccS : conjC_closed calS by exact: cfAut_seqInd.
have conjCS: cfConjC_subset calS (seqIndD H L H 1) by split.
case: R1gen @R1 => /= R1 subc1. 
have [[chi_char nrI ccI] tau_iso oI h1 hortho] := subc1.
pose R chi := flatten [seq R1 'chi_i | i in S_ chi].
have memI phi i: phi \in calS -> i \in S_ phi -> 'chi_i \in calI.
  by move=> Sphi Sphi_i; apply/image_f/S_calSP; exists phi.
have aux phi psi i j mu nu:
    phi \in calS -> psi \in calS ->
    i \in S_ phi -> j \in S_ psi -> 
    mu \in R1 'chi_i -> nu \in R1 'chi_j -> 
  orthogonal 'chi_i ('chi_j :: ('chi_j)^*%CF) -> '[mu, nu] = 0.
- move=> Sphi Spsi Sphi_i Spsi_j R1i_mu R1i_nu o_ij.
  apply: orthogonalP R1i_mu R1i_nu.
  by apply: hortho o_ij; [apply: memI Spsi Spsi_j | apply: memI Sphi Sphi_i].
exists R; split => //= => [| i Ii]; last first.
  have mem_i := chi_calI Ii; have{h1} [Zirr oR1 tau_im] := h1  _ mem_i.
  split=> //; apply/eqP; rewrite -eqC_nat -cfnorm_orthonormal // -{}tau_im.
  have ?: 'chi_i - ('chi_i)^*%CF \in 'Z[calI, L^#].
    have hchi : 'chi_i \in 'Z[calI, L] by rewrite mem_zchar_on // cfun_onG.
    rewrite sub_aut_zchar ?cfAut_zchar // => _ /mapP[j _ ->]; exact: irr_vchar.
  have [-> // _] := tau_iso; rewrite cfnormBd ?cfnorm_conjC ?cfnorm_irr //.
  by have [_ ->] := pairwise_orthogonalP oI; rewrite ?ccI // eq_sym (hasPn nrI).
have calS_portho : pairwise_orthogonal calS by exact: seqInd_orthogonal.
have calS_char : {subset calS <= character} by apply: seqInd_char.
have calS_chi_ortho :
  {in calS &, forall phi psi i j,
     i \in irr_constt phi -> j \in irr_constt psi ->
  '[phi, psi] = 0 -> '['chi_i, 'chi_j] = 0}.
- by move=> phi psi Sphi Spsi /= i j; apply: irr_constt_ortho; apply/calS_char.
have ZisoS_tau: {in 'Z[calS, L^#], isometry tau, to 'Z[irr G, G^#]}.
  apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
  have /subsetD1P[_ /setU1K <-] := FTsupp_sub L.
  rewrite zcharD1E zcharD1 => /andP[S_phi ->]; rewrite andbT.
  apply: zchar_trans_on phi S_phi => psi calS_psi.
  rewrite zchar_split (seqInd_vcharW calS_psi) /=.
  by have [Dpsi _ hCF] := PF_12_2a calS_psi; rewrite Dpsi rpred_sum. 
split=> {ZisoS_tau}//= [phi calS_phi | phi psi calS_phi calS_psi].
  rewrite /R /[seq _ | i in _]; set e := enum _; have: uniq e := enum_uniq _.
  have: all (mem (S_ phi)) e by apply/allP=> i; rewrite mem_enum.
  have ->: phi - phi^*%CF = \sum_(i <- e) ('chi_i - ('chi_i)^*%CF).
    by rewrite big_filter sumrB -rmorph_sum; have [<-] := PF_12_2a calS_phi.
  elim: e => /= [_ _ | i e IHe /andP[Si Se] /andP[e'i Ue]].
    by rewrite !big_nil /tau linear0.
  rewrite big_cons [tau _]linearD big_cat /= -/tau orthonormal_cat.
  have{IHe Ue} [/allP Ze -> ->] := IHe Se Ue.
  have{h1} /h1[/allP Z_R1i -> -> /=] := memI _ _ calS_phi Si.
  split=> //; first by apply/allP; rewrite all_cat Z_R1i.
  apply/orthogonalP=> mu nu R1i_mu /flatten_mapP[j e_j R1j_nu].
  have /= Sj := allP Se j e_j; apply: (aux phi phi i j) => //.
  rewrite /orthogonal /= !andbT !cfdot_irr mulrb ifN_eqC ?(memPn e'i) ?eqxx //=.
  rewrite !inE in Si Sj; rewrite -conjC_IirrE; set k := conjC_Iirr j.
  rewrite (calS_chi_ortho phi phi^*%CF) ?calS_char ?ccS //.
    by rewrite irr_consttE conjC_IirrE cfdot_conjC fmorph_eq0.
  by rewrite (seqInd_conjC_ortho _ _ _ calS_phi) ?mFT_odd.
case/andP=> /and3P[/eqP opsi_phi /eqP opsi_phiC _] _; apply/orthogonalP.
move=> nu mu /flatten_imageP[j Spsi_j R1j_nu] /flatten_imageP[i Sphi_i R1i_mu].
apply: (aux psi phi j i) => //; rewrite /orthogonal /= !andbT -conjC_IirrE.
rewrite !inE in Sphi_i Spsi_j; rewrite (calS_chi_ortho psi phi) ?calS_char //.
rewrite (calS_chi_ortho psi phi^*%CF) ?calS_char ?ccS ?eqxx //.
by rewrite irr_consttE conjC_IirrE cfdot_conjC fmorph_eq0.
Qed.

End Twelve2.

Local Notation R1gen := FPtype1_irr_subcoherent.
Local Notation Rgen := FPtype1_subcoherent.

(* This is Peterfalvi (12.3) *)
Lemma PF_12_3 L1 L2 (maxL1 : L1 \in 'M) (maxL2 : L2 \in 'M)
  (L1type : FTtype L1 == 1%N) (L2type : FTtype L2 == 1%N)
  (H1 := L1`_\F%G) (H2 := L2`_\F%G) 
  (calS1 := seqIndD H1 L1 H1 1) (calS2 := seqIndD H2 L2 H2 1) 
  (R1 := sval (Rgen maxL1 L1type)) (R2 := sval (Rgen maxL2 L2type)) : 
  (gval L2) \notin L1 :^: G ->
  {in calS1 & calS2, forall chi1 chi2, orthogonal (R1 chi1) (R2 chi2)}.
Proof.
wlog dA1A : L1 L2 maxL1 maxL2 @H1 @H2 L1type L2type @calS1 @calS2 @R1 @R2 / 
  [disjoint 'A1~(L2) & 'A~(L1)].
- move=> hwlog L12_non_conj.
  have [_ _] := (FT_Dade_support_disjoint maxL1 maxL2 L12_non_conj).
  case=> /hwlog => [dA1A chi1 chi2 Schi1 Schi2 |]; last exact.
  by rewrite orthogonal_sym dA1A // orbit_sym.
(* GG -- sorry, I don't plan switching ssreflect versions before the proof
   is over; please refrain from using 1.4-only features, for now
case: (X in sval X) @R1 => /= R1; set R1' := sval _ => [[subcoh1 hR1' defR1']].
case: (X in sval X) @R2 => /= R2; set R2' := sval _ => [[subcoh2 hR2' defR2']].
*)
case: (Rgen _ _) @R1 => /= R1; set R1' := sval _ => [[subcoh1 hR1' defR1]].
case: (Rgen _ _) @R2 => /= R2; set R2' := sval _ => [[subcoh2 hR2' defR2]].
move=> L12_non_conj chi1 chi2 calS1_chi1 calS2_chi2. 
apply/orthogonalP=> a b R1a R2b. 
pose tau1 := FT_Dade maxL1; pose tau2 := FT_Dade maxL2.
have [_ _ _ /(_ chi1 calS1_chi1)[Z_R1 /orthonormalP[R1_U oR1] dtau1_chi1] _] := subcoh1.
have Z1a: a \in dirr G by rewrite dirrE Z_R1 //= oR1 ?eqxx.
suffices{b R2b}: '[a, tau2 (chi2 - chi2^*%CF)] = 0.
  apply: contra_eq => nz_ab; rewrite /tau2. 
  have [_ _ _ /(_ chi2 calS2_chi2)[Z_R2 o1R2 ->] _] := subcoh2.
  suffices [e ->]: {e | a = if e then - b else b}.
    rewrite -scaler_sign cfdotC cfdotZr -cfdotZl scaler_sumr.
    by rewrite cfproj_sum_orthonormal // conjCK signr_eq0.
  have [_ oR2] := orthonormalP o1R2.
  have Z1b: b \in dirr G by rewrite dirrE Z_R2 //= oR2 ?eqxx.
  move/eqP: nz_ab; rewrite cfdot_dirr //.
  by do 2?[case: eqP => [-> | _]]; [exists true | exists false | ].
  case: (PF_12_2a maxL1 L1type calS1_chi1) =>  chi1D _ chi1_sup.
pose S_chi1 := [set i0 in irr_constt chi1].
have {chi1_sup} sub_conjC : {in S_chi1, forall i, exists k : Iirr G, 
  tau1 ('chi_i - ('chi_i)^*%CF) = 'chi_k - ('chi_k)^*%CF}.
- by move=> i /chi1_sup; apply: Dade_irr_sub_conjC.
have {sub_conjC dtau1_chi1 R1_U R1a defR1}[t S_ch1t et]: 
  exists2 t, t \in S_chi1 & tau1 ('chi_t - ('chi_t)^*%CF) = a - a^*%CF.
- suff /exists_inP[i iS_chi1 dota]: [exists (i | i \in S_chi1), 
    '[tau1 ('chi_i - (('chi_i)^*)%CF), a] > 0].
    have [k k_Schi1] := sub_conjC _ iS_chi1.
    suff /orP : (a == 'chi_k) || (a == - ('chi_k)^*%CF).
      by case=> /eqP ->; last (rewrite rmorphN /= opprK addrC cfConjCK); exists i.
    move: dota; rewrite {}k_Schi1 -conjC_IirrE cfdotBl.
    do 2! (rewrite cfdot_dirr // ?mem_dirr //).
    case: ifP=> h1; (case: ifP=> h2; first by rewrite (eqP h2) (opprK a) eqxx orbT).
    - case: ('chi_(conjC_Iirr k) == a); last first.
        by rewrite subr0 oppr_gt0 ltr10.
      rewrite -opprD real_ltrNge //; last by rewrite rpredN rpredD.
      by rewrite oppr_le0 addr_ge0 // ?ler01.
    - rewrite eq_sym; case: (a == 'chi_k) => //=.
      case: ('chi_(conjC_Iirr k) == a); last by rewrite subr0 ltrr.
      by rewrite sub0r oppr_gt0 ltr10.
  have : '[tau1 (chi1 - chi1^*%CF), a] == 1.
    rewrite /tau1 dtau1_chi1 (big_rem _ R1a) /= cfdotDl cfdot_suml oR1 // eqxx.
    rewrite big_seq_cond big1 ?addr0 // => i; rewrite andbT => hi.
    rewrite oR1 ?(mem_rem hi) //; move: hi; rewrite mem_rem_uniq // inE eq_sym. 
    by case/andP=> /negPf ->.
  apply: contraLR; rewrite negb_exists => /forallP abs.
  suff :  '[tau1 (chi1 - (chi1^*)%CF), a] <= 0.
    by apply: contraL => /eqP->; rewrite ler10.
  rewrite chi1D rmorph_sum /= -sumrB [tau1 _]linear_sum /= cfdot_suml.
  rewrite -oppr_ge0 -sumrN sumr_ge0 // => i Si; rewrite oppr_ge0 -/tau1.
  have := (abs i); rewrite Si /=; case/sub_conjC: Si=> k ->.
  rewrite -conjC_IirrE cfdotBl; do 2! (rewrite cfdot_dirr // ?mem_dirr //).
  case: ifP=> h1; case: ifP=> h2; first by move=> _; rewrite addrN lerr.
  - case: ('chi_(conjC_Iirr k) == a) => _; last by rewrite subr0 oppr_le0 ler01.
    by rewrite -opprB opprK oppr_le0 addr_ge0 ?ler01.
  - case eka : ('chi_k == a) => /=; last by rewrite opprK add0r ltr01.
  - by rewrite opprK addr_gt0 ?ltr01 //.
  - case: ('chi_k == a) => //=; case: ('chi_(conjC_Iirr k) == a) => //=.
    + by rewrite addrN lerr.
    + by rewrite subr0 ltr01.
    + by rewrite sub0r oppr_le0 ler01.
    + by rewrite subr0 lerr.
suff :  '[a, tau2 (chi2 - (chi2^*)%CF)] = - '[a, tau2 (chi2 - (chi2^*)%CF)].
  by move/eqP; rewrite -addr_eq0 -mulr2n mulrn_eq0 /=; move/eqP.
have {t S_ch1t et} : '[a - (a^*)%CF, tau2 (chi2 - (chi2^*)%CF)] == 0.
  set psi := chi2 - _; have A1psi: psi \in 'CF(L2, 'A1(L2)).
    apply: cfun_onS (Fcore_sub_FTsupp1 maxL2) _.
    have nH2L2 : H2 <| L2 by exact: gFnormal.
    by have /zchar_on := seqInd_sub_aut_zchar nH2L2 conjC calS2_chi2.
  rewrite [tau2 _]FT_DadeE ?(cfun_onS (FTsupp1_sub _)) // -FT_Dade1E //.
  rewrite -et (cfdot_complement (Dade_cfunS _ _)) //= setTD FT_Dade_supportE.
  apply: cfun_onS (Dade_cfunS _ _); rewrite FT_Dade1_supportE.
  by rewrite -disjoints_subset.
rewrite cfdotBl subr_eq0; move/eqP=> {1}->.
suff -> : '[a^*, tau2 (chi2 - (chi2^*)%CF)] = '[a, tau2 ((chi2^*)%CF - chi2)].
  by rewrite -opprB [tau2 _]linearN /= cfdotNr.
have -> : chi2 - (chi2^*)%CF = ((chi2^*)%CF - chi2)^*%CF.
  by rewrite rmorphB /= cfConjCK.
rewrite [tau2 _]Dade_conjC cfdot_conjC.
apply/eqP; rewrite -CrealE; apply: Creal_Cint.
apply: Cint_cfdot_vchar; first by move: Z1a; rewrite dirrE; case/andP.
rewrite -opprB linearN rpredN /=.
have [_ _ _ /(_ chi2 calS2_chi2)[Z_R2 /orthonormalP[_ oR2] ->] _] := subcoh2.
rewrite big_seq_cond rpred_sum // => i; rewrite andbT => irri.
have: i \in dirr G by rewrite dirrE Z_R2 //= oR2 ?eqxx.
by rewrite dirrE; case/andP.
Qed.

Section Twelve_4_to_6.

Variable L : {group gT}.
Hypothesis maxL : L \in 'M .

Local Notation "` 'L'" := (gval L) (at level 0, only parsing) : group_scope.
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F (at level 0) : group_scope.
Local Notation H' := H^`(1)%G.
Local Notation "` 'H''" := `H^`(1) (at level 0) : group_scope.

Let calS := seqIndD H L H 1%G.
Let tau := FT_Dade maxL.

Section Twelve_4_5.

Hypothesis Ltype : FTtype L == 1%N.

Let R := sval (Rgen maxL Ltype).
Let S_ (chi : 'CF(L)) := [set i in irr_constt chi].

(* This will be Peterfalvi (12.4). *)
Lemma FTtype1_ortho_constant (psi : 'CF(G)) x : 
    {in calS, forall phi, orthogonal psi (R phi)} -> x \in L :\: H ->
  {in x *: H, forall y, psi y = psi x}%g.
Proof. 
move=> hphi xLDH.
have nHL : H <| L by exact: gFnormal.
have [U [Utype _]] := FTtypeP _ maxL Ltype.
have [[_ _ sdHU] [U1 inertU1] _] := Utype.
have /= [_ _ [hT1 Nsub]]:= FTtypeI_II_facts maxL Ltype sdHU.
have Dade_hyp := FT_Dade_hyp maxL.
have dot_irr chi i : chi \in calS -> i \in S_ chi -> '['chi_i, chi] = 1.
  move=> chi_calS Si.
  have -> : chi = \sum_(i <- enum (S_ chi)) 'chi_i.
    case/(PF_12_2a maxL Ltype): chi_calS => {3}-> _ _. 
    by rewrite big_uniq ?enum_uniq //=; apply: eq_bigl => j; rewrite mem_enum.
  rewrite (bigD1_seq i) ?mem_enum ?enum_uniq //= cfdotDr cfdot_sumr cfnorm_irr.
  by rewrite big1 ?addr0 // => j i'j; rewrite cfdot_irr eq_sym (negPf i'j).
have supp12B y chi i1 i2 : chi \in calS -> i1 \in S_ chi -> i2 \in S_ chi ->
  y \notin ('A(L) :\: H^#) -> ('chi_i1 - 'chi_i2) y = 0.
- move=> calS_chi Si1 Si2 yADHn.
  have [chiD chi1 sup_chi] := PF_12_2a maxL Ltype calS_chi.
  have [Hy | H'y] := boolP (y \in H); last first.
    suffices /cfun_on0->: y \notin 1%g |: 'A(L) by rewrite ?rpredB ?sup_chi.
    by rewrite !inE negb_or negb_and (group1_contra H'y) ?H'y in yADHn *.
  have [s _ chiIndD] := seqIndP calS_chi.
  pose sum_sL := \sum_(chi_z <- ('chi_s ^: L)%CF) chi_z.
  suffices Dchi: {in S_ chi, forall i, 'chi_i y = sum_sL y}.
    by rewrite !cfunE !Dchi ?subrr.
  move=> i Si; pose phiH := 'Res[H] 'chi_i.
  transitivity (phiH y); first by rewrite cfResE ?normal_sub.
  have phiH_s_1: '[phiH, 'chi_s] = 1 by rewrite cfdot_Res_l -chiIndD dot_irr.
  have phiH_s: s \in irr_constt phiH by rewrite irr_consttE phiH_s_1 oner_eq0.
  by rewrite [phiH](Clifford_Res_sum_cfclass _ phiH_s) // phiH_s_1 scale1r.
have coh12 chi i1 i2 
  (calS12 := undup ('chi_i1 :: ('chi_i1)^*%CF :: 'chi_i2 :: ('chi_i2)^*%CF)) :
  chi \in calS -> i1 \in S_ chi -> i2 \in S_ chi -> coherent calS12 L^# tau.
  move=> calS_chi Si1 Si2; have [_ cst1 _]:= (PF_12_2a maxL Ltype calS_chi).
  case: (R1gen maxL Ltype) => R1 subcoh1.
  have calS12S : {subset calS12 <= [seq 'chi_i | i in Iirr_kerD L H 1%G]}.
    move=> xi; rewrite mem_undup.
    by case/or4P; rewrite ?orbF /= => /eqP ->; 
       rewrite ?cc_calI // map_f // mem_enum; apply/S_calSP; exists chi.
  have subcoh12 : subcoherent calS12 tau R1.
    apply: (subset_subcoherent subcoh1); rewrite /cfConjC_subset; split=> //.
    - by rewrite /calS12 undup_uniq.
    - rewrite /conjC_closed => phi; rewrite mem_undup /= /calS12.
      by case/or4P;  
        rewrite ?orbF => /eqP ->; rewrite ?cfConjCK mem_undup !inE eqxx ?orbT.
    have conjC_deg (i : Iirr L) : ('chi_i)^*%CF 1%g = 'chi_i 1%g.
      by rewrite cfunE irr1_degree rmorph_nat.
    apply: (uniform_degree_coherence subcoh12).
    (* no shortcut for subseq of a constant is constant? *)
    case/(constantP 0): cst1 => c /all_pred1P /allP => nseqD.
    apply: (@all_pred1_constant _ c); apply/allP=> _ /mapP[xi calSxi ->]. 
    apply/nseqD/imageP; move: calSxi; rewrite mem_undup !inE.
    by case/or4P=> /eqP->; by [exists i1 | exists i2].
admit.
Qed.

(* This will be Peterfalvi (12.5) *)
Let rho := invDade (FT_Dade_hyp maxL).
Lemma FtypeI_invDade_ortho_constant (psi : 'CF(G)) : 
    {in calS, forall phi, orthogonal psi (R phi)} ->
  {in H :\: H' &, forall x y, rho psi x = rho psi y}.
Proof. move: maxL Ltype; admit. Qed.

End Twelve_4_5.

Hypothesis frobL : [Frobenius L with kernel H].

Lemma FT_Frobenius_type1 : FTtype L == 1%N.
Proof.
have [E /Frobenius_of_typeF LtypeF] := existsP frobL.
by apply/idPn=> /FTtypeP_witness[]// _ _ _ _ _ /typePF_exclusion/(_ E).
Qed.

(* This will be (12.6). *)
Lemma FT_Frobenius_coherence : {subset calS <= irr L} /\ coherent calS L^# tau.
Proof. move: maxL frobL. admit. Qed.

End Twelve_4_to_6.

Section Twelve_8_to_16.

Variable p : nat.

(* Equivalent reformultaion of hypothesis 12.8, avoiding quotients. *)
Hypothesis IHp : forall q M, (q < p)%N -> M \in 'M -> FTtype M == 1%N ->  
  ('r_p(M) > 1)%N -> p \in \pi(M`_\F).

Variables M P0 : {group gT}.

Let K := M`_\F%G.
Let K' := M^`(1)%G.

Hypothesis maxM : M \in 'M.
Hypothesis Mtype1 : FTtype M == 1%N.
Hypothesis prankM : ('r_p (M) > 1)%N.
Hypothesis p'K : p^'.-group K.

Hypothesis Sylow_P0 :  p.-Sylow(M) P0.

Lemma PF12_9 :
  [/\ abelian P0, 'r_p(P0) = 2
    & exists2 L, L \in 'M /\ P0 \subset L`_\s
    & exists2 x, x \in 'Ohm_1(P0)^#
    & [/\ ~~ ('C_K[x] \subset K'), 'N(<[x]>) \subset M & ~~ ('C[x] \subset L)]].
Proof. move: IHp maxM Mtype1 prankM p'K Sylow_P0; admit. Qed.

Variables (L : {group gT}) (x : gT).
Hypotheses (abP0 : abelian P0) (prankP0 : 'r_p(P0) = 2).
Hypotheses (maxL : L \in 'M) (sP0_Ls : P0 \subset L`_\s).
Hypotheses (P0_1s_x : x \in 'Ohm_1(P0)^#) (sNxM : 'N(<[x]>) \subset M).
Hypothesis not_sCxK' : ~~ ('C_K[x] \subset K').
Hypothesis not_sCxL : ~~ ('C[x] \subset L).

Let H := L`_\F%G.

Let frobL : [Frobenius L with kernel H].
Proof.
move: PF12_9 abP0 prankP0 maxL sP0_Ls P0_1s_x sNxM not_sCxK' not_sCxL; admit.
Qed.

Let Ltype1 : FTtype L == 1%N. Proof. exact: FT_Frobenius_type1 frobL. Qed.

Let sP0H : P0 \subset H.
Proof. by have:= sP0_Ls; rewrite /L`_\s (eqP Ltype1). Qed.

Let defM : K ><| (M :&: L) = M.
Proof. move: frobL. admit. Qed.

Let sML_H : M :&: L \subset H.
Proof. move: frobL. admit. Qed.

Let E := sval (sigW (existsP frobL)).
Let e := #|E|.

Let defL : H ><| E = L.
Proof. by rewrite /E; case: (sigW _) => E0 /=/Frobenius_context[]. Qed.

Let Ecyclic_le_p : cyclic E /\ (e %| p.-1) || (e %| p.+1).
Proof.
pose P := 'O_p(H)%G; pose T := 'Ohm_1('Z(P))%G.
have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall p (Fcore_nil L).
have [[sPH pP _] [sP0M pP0 _]] := (and3P sylP, and3P Sylow_P0). 
have sP0P: P0 \subset P by rewrite (sub_normal_Hall sylP) ?pcore_normal.
have defP0: P :&: M = P0.
  rewrite [P :&: M](sub_pHall Sylow_P0 (pgroupS _ pP)) ?subsetIl ?subsetIr //.
  by rewrite subsetI sP0P.
have [ntx P01x] := setD1P P0_1s_x; have P0x := subsetP (Ohm_sub 1 P0) x P01x.
have sZP0: 'Z(P) \subset P0.
  apply: subset_trans (_ : 'C_P[x] \subset P0).
    by rewrite -cent_set1 setIS ?centS // sub1set (subsetP sP0P).
  by rewrite -defP0 setIS // (subset_trans _ sNxM) // cents_norm ?cent_cycle.
have ntT: T :!=: 1%g.
  rewrite Ohm1_eq1 center_nil_eq1 ?(pgroup_nil pP) // (subG1_contra sP0P) //.
  by apply/trivgPn; exists x.
have [_ sEL _ nHE tiHE] := sdprod_context defL.
have charTP: T \char P := char_trans (Ohm_char 1 _) (center_char P).
have{ntT} [V minV sVT]: {V : {group gT} | minnormal V E & V \subset T}.
  apply: mingroup_exists; rewrite ntT (char_norm_trans charTP) //.
  exact: char_norm_trans (pcore_char p H) nHE.
have abelT: p.-abelem T by rewrite Ohm1_abelem ?center_abelian ?(pgroupS sZP0).
have sTP := subset_trans (Ohm_sub 1 _) sZP0.
have rankT: ('r_p(T) <= 2)%N by rewrite -prankP0 p_rankS.
have [abelV /andP[ntV nVE]] := (abelemS sVT abelT, mingroupp minV).
have pV := abelem_pgroup abelV; have [pr_p _ [n oV]] := pgroup_pdiv pV ntV.
have frobHE: [Frobenius L = H ><| E] by rewrite /E; case: (sigW _).
have: ('r_p(V) <= 2)%N by rewrite (leq_trans (p_rankS p sVT)).
rewrite (p_rank_abelem abelV) // oV pfactorK // ltnS leq_eqVlt ltnS leqn0 orbC.
have sVH := subset_trans sVT (subset_trans (char_sub charTP) sPH).
have regVE: 'C_E(V) = 1%g.
  exact: cent_semiregular (Frobenius_reg_compl frobHE) sVH ntV.
case/pred2P=> dimV; rewrite {n}dimV in oV.
  pose f := [morphism of restrm nVE (conj_aut V)].
  have injf: 'injm f by rewrite ker_restrm ker_conj_aut regVE.
  rewrite /e -(injm_cyclic injf) // -(card_injm injf) //.
  have AutE: f @* E \subset Aut V by rewrite im_restrm Aut_conj_aut.
  rewrite (cyclicS AutE) ?Aut_prime_cyclic ?oV // (dvdn_trans (cardSg AutE)) //.
  by rewrite card_Aut_cyclic ?prime_cyclic ?oV // totient_pfactor ?muln1.
have defV: V :=: 'Ohm_1(P0).
  apply/eqP; rewrite eqEcard (subset_trans sVT) ?OhmS //= oV -prankP0.
  by rewrite p_rank_abelian // -card_pgroup ?(pgroupS (Ohm_sub 1 _)).
pose rE := abelem_repr abelV ntV nVE.
have ffulE: mx_faithful rE by apply: abelem_mx_faithful.
have p'E: [char 'F_p]^'.-group E.
  rewrite (eq_p'group _ (charf_eq (char_Fp pr_p))) (coprime_p'group _ pV) //.
  by rewrite coprime_sym (coprimeSg sVH) ?(Frobenius_coprime frobHE).
have dimV: 'dim V = 2 by rewrite (dim_abelemE abelV) // oV pfactorK. 
have cEE: abelian E.
  by rewrite dimV in (rE) ffulE; apply: charf'_GL2_abelian (mFT_odd E) ffulE _.
have Enonscalar y: y \in E -> y != 1%g -> ~~ is_scalar_mx (rE y).
  move=> Ey; apply: contra => /is_scalar_mxP[a rEy]; simpl in a.
  have nXy: y \in 'N(<[x]>).
    rewrite !inE -cycleJ cycle_subG; apply/cycleP; exists a.
    have [Vx nVy]: x \in V /\ y \in 'N(V) by rewrite (subsetP nVE) ?defV.
    apply: (@abelem_rV_inj p _ V); rewrite ?groupX ?memJ_norm ?morphX //=.
    by rewrite zmodXgE -scaler_nat natr_Zp -mul_mx_scalar -rEy -abelem_rV_J.
  rewrite -in_set1 -set1gE -tiHE inE (subsetP sML_H) //.
  by rewrite inE (subsetP sEL) // (subsetP sNxM).
have /trivgPn[y nty Ey]: E != 1%G by have [] := Frobenius_context frobHE.
have cErEy: centgmx rE (rE y).
  by apply/centgmxP=> z Ez; rewrite -!repr_mxM // (centsP cEE).
have irrE: mx_irreducible rE by apply/abelem_mx_irrP.
have charFp2: p \in [char MatrixGenField.gen_finFieldType irrE cErEy].
  apply: (rmorph_char (MatrixGenField.gen_rmorphism irrE cErEy)).
  exact: char_Fp.
pose Fp2 := primeChar_finFieldType charFp2.
pose n1 := MatrixGenField.gen_dim (rE y).
pose rEp2 : mx_representation Fp2 E n1 := MatrixGenField.gen_repr irrE cErEy.
have n1_gt0: (0 < n1)%N := MatrixGenField.gen_dim_gt0 irrE cErEy.
have n1_eq1: n1 = 1%N.
  pose d := degree_mxminpoly (rE y).
  have dgt0: (0 < d)%N := mxminpoly_nonconstant _.
  apply/eqP; rewrite eqn_leq n1_gt0 andbT -(leq_pmul2r dgt0).
  rewrite (MatrixGenField.gen_dim_factor irrE cErEy) mul1n dimV.
  by rewrite ltnNge mxminpoly_linear_is_scalar Enonscalar.
have oFp2: #|Fp2| = (p ^ 2)%N.
  rewrite card_sub card_matrix card_Fp // -{1}n1_eq1.
  by rewrite (MatrixGenField.gen_dim_factor irrE cErEy) dimV.
have [f rfK fK]: bijective (@scalar_mx Fp2 n1).
  rewrite n1_eq1.
  by exists (fun A : 'M_1 => A 0 0) => ?; rewrite ?mxE -?mx11_scalar.
pose g z : {unit Fp2} := insubd (1%g : {unit Fp2}) (f (rEp2 z)).
have val_g z : z \in E -> (val (g z))%:M = rEp2 z.
  move=> Ez; rewrite insubdK ?fK //; have:= repr_mx_unit rEp2 Ez.
  by rewrite -{1}[rEp2 z]fK unitmxE det_scalar !unitfE expf_eq0 n1_gt0.
have ffulEp2: mx_faithful rEp2 by rewrite MatrixGenField.gen_mx_faithful.
have gM: {in E &, {morph g: z1 z2 / z1 * z2}}%g.
  move=> z1 z2 Ez1 Ez2 /=; apply/val_inj/(can_inj rfK).
  rewrite {1}(val_g _ (groupM Ez1 Ez2)) scalar_mxM.
  by rewrite {1}(val_g _ Ez1) (val_g _ Ez2) repr_mxM.
have inj_g: 'injm (Morphism gM).
  apply/injmP=> z1 z2 Ez1 Ez2 /(congr1 (@scalar_mx _ n1 \o val)).
  by rewrite /= {1}(val_g _ Ez1) (val_g _ Ez2); apply: mx_faithful_inj.
split; first by rewrite -(injm_cyclic inj_g) ?field_unit_group_cyclic.
have: e %| #|[set: {unit Fp2}]|.
  by rewrite /e -(card_injm inj_g) ?cardSg ?subsetT.
rewrite card_finField_unit oFp2 -!subn1 (subn_sqr p 1) addn1.
rewrite orbC Gauss_dvdr; first by move->.
rewrite coprime_sym coprime_has_primes ?subn_gt0 ?prime_gt1 ?cardG_gt0 //.
apply/hasPn=> r; rewrite /= !mem_primes subn_gt0 prime_gt1 ?cardG_gt0 //=.
case/andP=> pr_r /Cauchy[//|z Ez oz]; rewrite pr_r /= subn1.
apply: contra (Enonscalar z Ez _); last by rewrite -order_gt1 oz prime_gt1.
rewrite -oz -(order_injm inj_g) // order_dvdn -val_eqE => /eqP gz_p1_eq1.
have /vlineP[a Dgz]: val (g z) \in 1%VS.
  rewrite Fermat's_little_theorem dimv1 card_Fp //=.
  by rewrite -[(p ^ 1)%N]prednK ?prime_gt0 // exprS -val_unitX gz_p1_eq1 mulr1.
apply/is_scalar_mxP; exists a; apply/row_matrixP=> i.
apply: (can_inj ((MatrixGenField.in_genK irrE cErEy) _)).
rewrite !rowE mul_mx_scalar MatrixGenField.in_genZ MatrixGenField.in_genJ //.
rewrite -val_g // Dgz mul_mx_scalar; congr (_ *: _).
rewrite -(natr_Zp a) scaler_nat.
by rewrite -(rmorph_nat (MatrixGenField.gen_rmorphism irrE cErEy)).
Qed.

Let calS := seqIndD H L H 1.
Notation tauL := (FT_Dade maxL).
Notation rhoL := (invDade (FT_Dade_hyp maxL)).

Section Twelve_13_to_16.

Variables (tau1 : {additive 'CF(L) -> 'CF(G)}) (chi : 'CF(L)).
Hypothesis cohS : coherent_with calS L^# tauL tau1.
Hypotheses (Schi : chi \in calS) (chi1 : chi 1%g = e%:R).
Let psi := tau1 chi.

Let rhoL_psi : {in K, forall g, psi (x * g)%g = chi x} /\ rhoL psi x = chi x.
Proof.
have nsHL: H <| L by rewrite gFnormal.
have nH1L: L \subset 'N(H^#) by rewrite normD1 gFnorm.
pose ddLH := restr_Dade_hyp (FT_Dade_hyp maxL) (Fcore_sub_FTsupp maxL) nH1L.
have defA: 'A(L) = H^#.
  apply/eqP; rewrite eqEsubset Fcore_sub_FTsupp // andbT.
  apply/bigcupsP=> y; rewrite /'A1(L) /L`_\s (eqP Ltype1) /= => H1y.
  by rewrite setSD //; have [_ _ _ ->] := Frobenius_kerP frobL.
pose tauL_H := Dade ddLH; pose rhoL_H := invDade ddLH.
have ->: rhoL psi = rhoL_H psi.
  by apply/cfunP=> y; rewrite !cfunElock /Dade_signalizer defA.
have not_LGM: gval M \notin L :^: G.
  apply: contraL p'K => /= /imsetP[z _ ->]; rewrite FcoreJ pgroupJ.
  by rewrite p'groupEpi (piSg sP0H) // -p_rank_gt0 prankP0.
pose rmR := sval (Rgen maxL Ltype1).
have Zpsi: psi \in 'Z[rmR chi].
  case: (Rgen _ _) @rmR => /= rmR []; rewrite -/calS => scohS _ _.
  have sSS: cfConjC_subset calS calS by apply: seqInd_conjC_subset1.
  have [B /mem_subseq sBR Dpsi] := mem_coherent_sum_subseq scohS sSS cohS Schi.
  by rewrite [psi]Dpsi big_seq rpred_sum // => xi /sBR/mem_zchar->.
have [ntx /(subsetP (Ohm_sub 1 P0))P0x] := setD1P P0_1s_x.
have Mx: x \in M by rewrite (subsetP sNxM) // -cycle_subG normG.
have psi_xK: {in K, forall g, psi (x * g)%g = psi x}.
  move=> g Kg; have{Kg}: (x * g \in x *: K)%g by rewrite mem_lcoset mulKg.
  apply: FTtype1_ortho_constant => [phi calMphi|].
    apply/orthoPl=> nu /memv_span; apply: {nu}span_orthogonal (zchar_span Zpsi).
    exact: PF_12_3.
  rewrite inE -/K (contra _ ntx) // => Kx.
  rewrite -(consttC p x) !(constt1P _) ?mulg1 ?(mem_p_elt p'K) //.
  by rewrite p_eltNK (mem_p_elt (pHall_pgroup Sylow_P0)).
have H1x: x \in H^# by rewrite !inE ntx (subsetP sP0H).
have rhoL_psi_x: rhoL_H psi x = psi x.
  rewrite cfunElock (restr_Dade_signalizer _ _ (def_FTsignalizer _)) // H1x.
  apply: canLR (mulKf (neq0CG _)) _; rewrite mulr_natl -sumr_const.
  apply: eq_bigr => g; rewrite /'R_L (negPf not_sCxL) /= setIC => /setIP[cxz].
  have Dx: x \in [set y in 'A0(L) | ~~ ('C[y] \subset L)].
    by rewrite inE (subsetP (Fcore_sub_FTsupp0 _)).
  have [_ [_ /(_ x Dx)defNx] _] := FTsupport_facts maxL.
  rewrite (cent1P cxz) -(eq_uniq_mmax defNx maxM) => [/psi_xK//|].
  by rewrite /= -cent_cycle (subset_trans (cent_sub _)).
suffices <-: (rhoL_H psi) x = chi x by split=> // g /psi_xK->.
have cohS_H: coherent_with calS H^# tauL_H tau1.
  have [IZtau Dtau] := cohS; split=> // xi Hxi.
  by rewrite [tauL_H _]restr_DadeE ?(zchar_on Hxi) ?Dtau ?zcharD1_seqInd.
have irrS: {subset calS <= irr L} by have [] := FT_Frobenius_coherence maxL.
have /irrP[t Dchi] := irrS _ Schi; have St: 'chi_t \in calS by rewrite -Dchi.
have Sgt1: (1 < size calS)%N by apply: seqInd_nontrivial St; rewrite ?mFT_odd.
have De: #|L : H| = e by rewrite -(index_sdprod defL).
have:= Dade_Ind1_sub_lin cohS_H Sgt1 St; rewrite -Dchi -/tauL_H -/calS -/psi /=.
set alpha := 'Ind 1 - chi; rewrite De => [[]] // [[o_tau_1 tau_alpha_1 _]].
case=> Gamma [o_tau1_Ga _ [a Za tau_alpha] _] _.
have [[Itau1 _] Dtau1] := cohS_H.
have o1calS: orthonormal calS.
  by rewrite (sub_orthonormal irrS) ?seqInd_uniq ?irr_orthonormal.
have norm_alpha: '[tauL_H alpha] = e%:R + 1.
  rewrite Dade_isometry ?(cfInd1_sub_lin_on _ Schi) ?De //.
  rewrite cfnormBd; last by rewrite cfdotC (seqInd_ortho_Ind1 _ _ Schi) ?conjC0.
  by rewrite cfnorm_Ind_cfun1 // De Dchi cfnorm_irr.
pose h := #|H|; have ub_a: a ^+ 2 * ((h%:R - 1) / e%:R) - 2%:R * a <= e%:R - 1.
  rewrite -[h%:R - 1](mulKf (neq0CiG L H)) -sum_seqIndC1_square // De -/calS.
  rewrite -[lhs in lhs - 1](addrK 1) -norm_alpha -[tauL_H _](subrK 1).
  rewrite cfnormDd; last by rewrite cfdotBl tau_alpha_1 cfnorm1 subrr.
  rewrite cfnorm1 addrK [in '[_]]addrC {}tau_alpha -!addrA addKr addrCA addrA.
  rewrite ler_subr_addr cfnormDd ?ler_paddr ?cfnorm_ge0 //; last first.
    rewrite cfdotBl cfdotZl cfdot_suml (orthoPr o_tau1_Ga) ?map_f // subr0.
    rewrite big1_seq ?mulr0 // => xi Sxi; rewrite cfdotZl.
    by rewrite (orthoPr o_tau1_Ga) ?map_f ?mulr0.
  rewrite cfnormB cfnormZ Cint_normK // cfdotZl cfproj_sum_orthonormal //.
  rewrite cfnorm_sum_orthonormal // Itau1 ?mem_zchar // irrWnorm ?irrS // divr1.
  rewrite chi1 divff ?neq0CG // mulr1 conj_Cint // addrAC mulr_natl.
  rewrite !ler_add2r !(mulr_suml, mulr_sumr) !big_seq ler_sum // => xi Sxi.
  rewrite irrWnorm ?irrS // !divr1 (mulrAC _^-1) -expr2 -!exprMn (mulrC _^-1).
  by rewrite normf_div normr_nat norm_Cnat // (Cnat_seqInd1 Sxi).
have [pr_p p_dv_M]: prime p /\ p %| #|M|.
  have: p \in \pi(M) by rewrite -p_rank_gt0 ltnW.
  by rewrite mem_primes => /and3P[].
have odd_p: odd p by rewrite (dvdn_odd p_dv_M) ?mFT_odd.
have pgt2: (2 < p)%N := odd_prime_gt2 odd_p pr_p.
have ub_e: e%:R <= (p%:R + 1) / 2%:R :> algC.
  rewrite ler_pdivl_mulr ?ltr0n // -natrM -mulrSr leC_nat.
  have [b e_dv_pb]: exists b : bool, e %| (b.*2 + p).-1.
    by have [_ /orP[]] := Ecyclic_le_p; [exists false | exists true].
  apply: (@leq_trans (b.*2 + p).-1); last first.
    by case: {e_dv_pb}b => //=; rewrite -subn1 leq_subLR !leqW.
  apply: dvdn_leq; first by rewrite -(subnKC pgt2) !addnS.
  rewrite Gauss_dvd ?coprimen2 ?mFT_odd // e_dv_pb dvdn2 -subn1.
  by rewrite -addnBA ?odd_add ?odd_sub ?prime_gt0 // odd_double odd_p.
have lb_h: p%:R ^+ 2 <= h%:R :> algC.
  rewrite -natrX leC_nat dvdn_leq ?pfactor_dvdn ?cardG_gt0 //.
  by rewrite -prankP0 (leq_trans (p_rankS p sP0H)) ?p_rank_le_logn.
have{ub_a ub_e} ub_a: p.-1.*2%:R * a ^+ 2 - 2%:R * a <= p.-1%:R / 2%:R :> algC.
  apply: ler_trans (ler_trans ub_a _); last first.
    rewrite -subn1 -subSS natrB ?ltnS ?prime_gt0 // mulrSr mulrBl.
    by rewrite divff ?pnatr_eq0 ?ler_add2r.
  rewrite ler_add2r mulrC -Cint_normK // -!mulrA !ler_wpmul2l ?normr_ge0 //.
  rewrite ler_pdivl_mulr ?gt0CG // ler_subr_addr (ler_trans _ lb_h) //.
  rewrite -muln2 natrM -mulrA -ler_subr_addr subr_sqr_1.
  rewrite -(natrB _ (prime_gt0 pr_p)) subn1 ler_wpmul2l ?ler0n //.
  by rewrite mulrC -ler_pdivl_mulr ?ltr0n.
have a0: a = 0.
  apply: contraTeq ub_a => nz_a; rewrite ltr_geF // ltr_pdivr_mulr ?ltr0n //.
  rewrite mulrC -{1}mulr_natl -muln2 natrM -mulrA mulrBr mulrCA ltr_subr_addl.
  rewrite -ltr_subr_addr -mulrBr mulr_natl mulrA -expr2 -exprMn.
  apply: ltr_le_trans (_ : 2%:R * ((a *+ 2) ^+ 2 - 1) <= _); last first.
    rewrite (mulr_natl a 2) ler_wpmul2r // ?subr_ge0.
      by rewrite sqr_Cint_ge1 ?rpredMn // mulrn_eq0.
    by rewrite leC_nat -subn1 ltn_subRL.
  rewrite -(@ltr_pmul2l _ 2%:R) ?ltr0n // !mulrA -expr2 mulrBr -exprMn mulr1.
  rewrite -natrX 2!mulrnAr -[in rhs in _ < rhs]mulrnAl -mulrnA.
  rewrite ltr_subr_addl -ltr_subr_addr -(ltr_add2r 1) -mulrSr -sqrrB1.
  rewrite -Cint_normK ?rpredB ?rpredM ?rpred_nat ?rpred1 //.
  rewrite (@ltr_le_trans _ (3 ^ 2)%:R) ?ltC_nat // natrX.
  rewrite ler_sqr ?qualifE ?ler0n ?normr_ge0 //.
  rewrite (ler_trans _ (ler_sub_dist _ _)) // normr1 normrM normr_nat.
  by rewrite ler_subr_addl -mulrS mulr_natl ler_pmuln2r ?norm_Cint_ge1.
pose chi0 := 'Ind[L, H] 1.
have defS1: perm_eq (seqIndT H L) (chi0 :: calS).
  by rewrite [calS]seqIndC1_rem // perm_to_rem ?seqIndT_Ind1.
have [c _ -> // _] := invDade_seqInd_sum ddLH psi defS1.
have psi_alpha_1: '[psi, tauL_H alpha] = -1.
  rewrite tau_alpha a0 scale0r addr0 addrC addrA cfdotBr cfdotDr.
  rewrite (orthoPr o_tau_1) ?(orthoPr o_tau1_Ga) ?map_f // !add0r.
  by rewrite Itau1 ?mem_zchar ?map_f // irrWnorm ?irrS.
rewrite (bigD1_seq chi) ?seqInd_uniq //= big1_seq => [|xi /andP[chi'xi Sxi]].
  rewrite addr0 -cfdotC chi1 cfInd1 ?gFsub // cfun11 mulr1 De divff ?neq0CG //.
  rewrite scale1r -opprB linearN cfdotNr psi_alpha_1 opprK.
  by rewrite irrWnorm ?irrS // divr1 mul1r.
rewrite -cfdotC cfInd1 ?gFsub // cfun11 mulr1.
rewrite /chi0 -(canLR (subrK _) (erefl alpha)) scalerDr opprD addrCA -scaleNr.
rewrite linearD linearZ /= cfdotDr cfdotZr psi_alpha_1 mulrN1 rmorphN opprK.
rewrite -/tauL_H -Dtau1 ?(seqInd_sub_lin_vchar _ Schi) ?De //.
have [_ ooS] := orthonormalP o1calS.
rewrite raddfB cfdotBr Itau1 ?mem_zchar // ooS // mulrb ifN_eqC // add0r.
rewrite -De raddfZ_Cnat ?(dvd_index_seqInd1 _ Sxi) // De cfdotZr.
by rewrite Itau1 ?mem_zchar ?ooS // eqxx mulr1 subrr !mul0r.
Qed.

Let rhoM := (invDade (FT_Dade1_hyp maxL)).

Let PF12_15 :
  [/\ {in K^#, forall g, rhoM psi g = psi g},
      {in K :\: K' &, forall g1 g2, psi g1 = psi g2}
    & {in K :\: K', forall g, psi g \in Cint}].
Proof. move: rhoL_psi; admit. Qed.

Lemma PF12_16_inner : False.
Proof. move: rhoL_psi; admit. Qed.

End Twelve_13_to_16.

(* Lemma PF12_16 : False. *)
(* Proof. Qed. *)

End Twelve_8_to_16.

(* This will be (12.7). *)
Theorem FTtype1_Frobenius M :
  M \in 'M -> FTtype M == 1%N -> [Frobenius M with kernel M`_\F].
Admitted. (* A cinch! *)

(* This will be (12.17). *)
Theorem not_all_FTtype1 : ~~ all_FTtype1 gT.
Admitted.


End PFTwelve.


