(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg finset center.
Require Import fingroup morphism perm automorphism quotient action finalg zmodp.
Require Import gfunctor gproduct cyclic commutator gseries nilpotent pgroup.
Require Import sylow hall abelian maximal frobenius.
Require Import matrix mxalgebra mxpoly mxrepresentation mxabelem vector.
Require Import falgebra fieldext finfield.
Require Import BGsection1 BGsection2 BGsection3 BGsection4 BGsection7.
Require Import BGsection14 BGsection15 BGsection16.
Require Import ssrnum ssrint algC cyclotomic algnum.
Require Import classfun character inertia vcharacter.
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

Section MoreFrobenius.
Import GroupScope.
Variables (gT : finGroupType) (G K H : {group gT}).

Lemma set_Frobenius_compl :
  K ><| H = G -> [Frobenius G with kernel K] -> [Frobenius G = K ><| H].
Proof.
move=> defG /Frobenius_kerP[ntK ltKG _ regKG].
apply/Frobenius_semiregularP=> //.
  by apply: contraTneq ltKG => H_1; rewrite -defG H_1 sdprodg1 properxx.
apply: semiregular_sym => y /regKG sCyK.
have [_ sHG _ _ tiKH] := sdprod_context defG.
by apply/trivgP; rewrite /= -(setIidPr sHG) setIAC -tiKH setSI.
Qed.

Lemma semiregularS (K1 K2 : {group gT}) (A1 A2 : {set gT}) :
  K1 \subset K2 -> A1 \subset A2 -> semiregular K2 A2 -> semiregular K1 A1.
Proof.
move=> sK12 sA12 regKA2 x /setD1P[ntx /(subsetP sA12)A2x].
by apply/trivgP; rewrite -(regKA2 x) ?inE ?ntx ?setSI.
Qed.

Lemma semiprimeS (K1 K2 : {group gT}) (A1 A2 : {set gT}) :
  K1 \subset K2 -> A1 \subset A2 -> semiprime K2 A2 -> semiprime K1 A1.
Proof.
move=> sK12 sA12 prKA2 x /setD1P[ntx A1x].
apply/eqP; rewrite eqEsubset andbC -{1}cent_set1 setIS ?centS ?sub1set //=.
rewrite -(setIidPl sK12) -!setIA prKA2 ?setIS ?centS //.
by rewrite !inE ntx (subsetP sA12).
Qed.

Lemma Frobenius_kerS (G1 : {group gT}) :
    G1 \subset G -> K \proper G1 ->
  [Frobenius G with kernel K] -> [Frobenius G1 with kernel K].
Proof.
move=> sG1G ltKG1 /Frobenius_kerP[ntK _ /andP[_ nKG] regKG].
apply/Frobenius_kerP; rewrite /normal proper_sub // (subset_trans sG1G) //.
by split=> // x /regKG; apply: subset_trans; rewrite setSI.
Qed.

End MoreFrobenius.

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

Let calX := Iirr_kerD L H 1%g.

Let calI := [seq 'chi_i | i in calX].

Let mem_calI i : i \in calX -> 'chi_i \in calI.
Proof. by move=> i_Iirr; apply/imageP; exists i. Qed.

Lemma FTtype1_irrP i : 
  reflect (exists2 chi, chi \in calS & i \in S_ chi) (i \in calX).
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

Lemma FTtype1_irr_partition : partition [set Si in [seq S_ chi | chi <- calS]] calX.
Proof.
have nsHL : H <| L by exact: gFnormal.
apply/and3P; split; last 1 first.
- rewrite inE; apply/mapP=> [[chi Schi /esym/setP S_0]].
  have /eqP[] := seqInd_neq0 nsHL Schi.
  rewrite [chi]cfun_sum_constt big1 // => i chi_i.
  by have:= S_0 i; rewrite inE chi_i inE.
- apply/eqP/setP=> i; apply/bigcupP/FTtype1_irrP=> [[S_chi] | [chi Schi Si]].
    by rewrite inE => /mapP[chi Schi ->]; exists chi.
  by exists (S_ chi); rewrite // inE map_f.
apply/trivIsetP=> S_chi1 S_chi2.
rewrite !inE => /mapP[chi1 Schi1 ->] /mapP[chi2 Schi2 ->] {S_chi1 S_chi2} chi2'1.
apply/pred0P=> i; rewrite /= !inE; apply/andP=> [[chi1_i chi2_i]].
suffices: '['chi_i] == 0 by rewrite cfnorm_irr oner_eq0.
rewrite (irr_constt_ortho (seqInd_char Schi1) (seqInd_char Schi2)) //.
by rewrite (seqInd_ortho _ Schi1 Schi2) // (contraNneq _ chi2'1) // => ->.
Qed.

(* This is Peterfalvi (12.2)(a), first part *)
Lemma FTtype1_seqInd_facts chi :
    chi \in calS ->
  [/\ chi = \sum_(i in S_ chi) 'chi_i,
      constant [seq 'chi_i 1%g | i in S_ chi]
    & {in S_ chi, forall i, 'chi_i \in 'CF(L, 1%g |: 'A(L))}].
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
have: j \in calX by apply/FTtype1_irrP; exists chi.
by rewrite !inE => /andP[/not_in_ker_char0->].
Qed.

(* This is Peterfalvi (12.2)(a), second part *)
Lemma FPtype1_irr_isometry :
  {in 'Z[calI, L^#], isometry tau, to 'Z[irr G, G^#]}.
Proof.
apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
rewrite zcharD1E => /andP[S_phi phi1_0].
have /subsetD1P[_ /setU1K <-] := FTsupp_sub L; rewrite zcharD1 {}phi1_0 andbT.
apply: zchar_trans_on phi S_phi => _ /imageP[i /FTtype1_irrP[j calSj Sj_i] ->].
by rewrite zchar_split irr_vchar; have [_ _ ->] := FTtype1_seqInd_facts calSj.
Qed.

Lemma FPtype1_irr_subcoherent : 
  {R : 'CF(L) -> seq 'CF(G) | subcoherent calI tau R}.
Proof.
apply: irr_subcoherent; last exact: FPtype1_irr_isometry.
  have UcalI: uniq calI by apply/dinjectiveP; apply: in2W irr_inj.
  split=> // _ /imageP[i Ii ->]; rewrite !inE in Ii; first exact: mem_irr.
  by apply/imageP; exists (conjC_Iirr i); rewrite ?inE conjC_IirrE ?cfker_aut.
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
  by move=> Sphi Sphi_i; apply/image_f/FTtype1_irrP; exists phi.
have aux phi psi i j mu nu:
    phi \in calS -> psi \in calS -> i \in S_ phi -> j \in S_ psi -> 
    mu \in R1 'chi_i -> nu \in R1 'chi_j -> 
  orthogonal 'chi_i ('chi_j :: ('chi_j)^*%CF) -> '[mu, nu] = 0.
- move=> Sphi Spsi Sphi_i Spsi_j R1i_mu R1i_nu o_ij.
  apply: orthogonalP R1i_mu R1i_nu.
  by apply: hortho o_ij; [apply: memI Spsi Spsi_j | apply: memI Sphi Sphi_i].
exists R; split => //= => [| i Ii]; last first.
  have mem_i := mem_calI Ii; have{h1} [Zirr oR1 tau_im] := h1  _ mem_i.
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
  have [Dpsi _ hCF] := FTtype1_seqInd_facts calS_psi.
  by rewrite zchar_split (seqInd_vcharW calS_psi) /= Dpsi rpred_sum.
split=> {ZisoS_tau}//= [phi calS_phi | phi psi calS_phi calS_psi].
  rewrite /R /[seq _ | i in _]; set e := enum _; have: uniq e := enum_uniq _.
  have: all (mem (S_ phi)) e by apply/allP=> i; rewrite mem_enum.
  have ->: phi - phi^*%CF = \sum_(i <- e) ('chi_i - ('chi_i)^*%CF).
    rewrite big_filter sumrB -rmorph_sum.
    by have [<-] := FTtype1_seqInd_facts calS_phi.
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
Lemma FTtype1_seqInd_ortho L1 L2 (maxL1 : L1 \in 'M) (maxL2 : L2 \in 'M)
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
pose tau1 := FT_Dade maxL1; pose tau2 := FT_Dade maxL2.
move=> L12_non_conj chi1 chi2 calS1_chi1 calS2_chi2. 
have [_ _ _ /(_ chi1 calS1_chi1)[Z_R1 o1R1 dtau1_chi1] _] := subcoh1.
have{o1R1} [uR1 oR1] := orthonormalP o1R1.
apply/orthogonalP=> a b R1a R2b; pose psi2 := tau2 (chi2 - chi2^*%CF).
have Z1a: a \in dirr G by rewrite dirrE Z_R1 //= oR1 ?eqxx.
suffices{b R2b}: '[a, psi2] == 0.
  apply: contraTeq => nz_ab; rewrite /psi2 /tau2. 
  have [_ _ _ /(_ chi2 calS2_chi2)[Z_R2 o1R2 ->] _] := subcoh2.
  suffices [e ->]: {e | a = if e then - b else b}.
    rewrite -scaler_sign cfdotC cfdotZr -cfdotZl scaler_sumr.
    by rewrite cfproj_sum_orthonormal // conjCK signr_eq0.
  have [_ oR2] := orthonormalP o1R2.
  have Z1b: b \in dirr G by rewrite dirrE Z_R2 //= oR2 ?eqxx.
  move/eqP: nz_ab; rewrite cfdot_dirr //.
  by do 2?[case: eqP => [-> | _]]; [exists true | exists false | ].
have [chi1D _ Achi1] := FTtype1_seqInd_facts maxL1 L1type calS1_chi1.
pose S_chi1 := [set i0 in irr_constt chi1].
pose bchi i := 'chi[_ : {set gT}]_i - ('chi_i)^*%CF.
have [t S_chi1t et]: exists2 t, t \in S_chi1 & tau1 (bchi _ t) = a - a^*%CF.
  suffices: ~~ [forall i in S_chi1, '[tau1 (bchi L1 i), a] <= 0].
    rewrite negb_forall_in => /exists_inP[i Si tau1i_a]; exists i => //.
    case/dIrrP: Z1a tau1i_a => ia ->.
    have [k ->]: exists k, tau1 (bchi _ i) = bchi G k.
      exact: Dade_irr_sub_conjC (Achi1 i Si).
    have {1}->: bchi G k = dchi (false, k) + dchi (true, conjC_Iirr k).
      by rewrite /dchi !scaler_sign conjC_IirrE.
    rewrite cfdotDl !cfdot_dchi addrACA -opprD subr_le0 -!natrD leC_nat.
    do 2?case: (_ =P ia) => [<-|] _ //; first by rewrite /dchi scale1r.
    by rewrite /dchi scaleN1r conjC_IirrE rmorphN /= cfConjCK opprK addrC.
  have: '[tau1 (chi1 - chi1^*%CF), a] == 1.
    rewrite /tau1 dtau1_chi1 (bigD1_seq a) //= cfdotDl cfdot_suml oR1 // eqxx.
    by rewrite big1_seq ?addr0 // => xi /andP[/negPf a'xi ?]; rewrite oR1 ?a'xi.
  apply: contraL => /forall_inP tau1a_le0.
  rewrite (ltr_eqF (ler_lt_trans _ ltr01)) // chi1D rmorph_sum /= -/S_chi1.
  rewrite -sumrB [tau1 _]linear_sum /= -/tau1 cfdot_suml.
  by rewrite -oppr_ge0 -sumrN sumr_ge0 // => i /tau1a_le0; rewrite oppr_ge0.
clear Achi1 dtau1_chi1 uR1 defR1.
suffices: '[a, psi2] == - '[a, psi2] by rewrite -addr_eq0 (mulrn_eq0 _ 2).
have A1bchi2: chi2 - (chi2^*)%CF \in 'Z[calS2, 'A1(L2)].
  by rewrite /'A1(_) /L2`_\s (eqP L2type) seqInd_sub_aut_zchar ?gFnormal.
have{t S_chi1t et} /eqP{2}->: '[a, psi2] == '[a^*%CF, psi2].
  move/zchar_on in A1bchi2; rewrite -subr_eq0 -cfdotBl.
  rewrite [psi2]FT_DadeE ?(cfun_onS (FTsupp1_sub _)) // -FT_Dade1E // -et.
  rewrite (cfdot_complement (Dade_cfunS _ _)) ?(cfun_onS _ (Dade_cfunS _ _)) //.
  by rewrite FT_Dade_supportE FT_Dade1_supportE setTD -disjoints_subset.
rewrite -2!raddfN opprB /= cfdot_conjCl -Dade_conjC rmorphB /= cfConjCK -/tau2.
rewrite conj_Cint ?Cint_cfdot_vchar ?(Z_R1 a) // Dade_vchar //.
rewrite (zchar_onS (FTsupp1_sub _)) // (zchar_sub_irr _ A1bchi2) //.
exact: seqInd_vcharW.
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
    by rewrite big_filter; have [] := FTtype1_seqInd_facts maxL Ltype chi_calS.
  rewrite (bigD1_seq i) ?mem_enum ?enum_uniq //= cfdotDr cfdot_sumr cfnorm_irr.
  by rewrite big1 ?addr0 // => j i'j; rewrite cfdot_irr eq_sym (negPf i'j).
have supp12B y chi i1 i2 : chi \in calS -> i1 \in S_ chi -> i2 \in S_ chi ->
  y \notin ('A(L) :\: H^#) -> ('chi_i1 - 'chi_i2) y = 0.
- move=> calS_chi Si1 Si2 yADHn.
  have [chiD chi1 sup_chi] := FTtype1_seqInd_facts maxL Ltype calS_chi.
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
  move=> calS_chi Si1 Si2; case: (R1gen maxL Ltype) => R1 subcoh1.
  have [_ cst1 _] := FTtype1_seqInd_facts maxL Ltype calS_chi.
  have calS12S : {subset calS12 <= [seq 'chi_i | i in Iirr_kerD L H 1%G]}.
    have [_ [[_ _ ccI] _ _ _ _]] := R1gen maxL Ltype.
    move=> xi /=; rewrite mem_undup; move: xi; apply/allP=> /=.
    by rewrite !ccI !image_f //; apply/FTtype1_irrP; exists chi.
  have subcoh12: subcoherent calS12 tau R1.
    apply: (subset_subcoherent subcoh1); rewrite /cfConjC_subset; split=> //.
    - by rewrite /calS12 undup_uniq.
    - rewrite /conjC_closed => phi; rewrite !mem_undup /=; move: phi.
      by apply/allP; rewrite /= !cfConjCK !inE !eqxx !orbT.
    have conjC_deg i: ('chi[L]_i)^*%CF 1%g = 'chi_i 1%g.
      by rewrite cfunE -irr_inv invg1.
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
Hypothesis IHp :
  forall q M, (q < p)%N -> M \in 'M -> FTtype M == 1%N -> ('r_q(M) > 1)%N ->
  q \in \pi(M`_\F).

Variables M P0 : {group gT}.

Let K := M`_\F%G.
Let K' := K^`(1)%G.

Hypothesis maxM : M \in 'M.
Hypothesis Mtype1 : FTtype M == 1%N.
Hypothesis prankM : ('r_p(M) > 1)%N.
Hypothesis p'K : p^'.-group K.

Hypothesis sylP0 : p.-Sylow(M) P0.

Lemma non_Frobenius_FTtype1_witness :
  [/\ abelian P0, 'r_p(P0) = 2
    & exists2 L, L \in 'M /\ P0 \subset L`_\s
    & exists2 x, x \in 'Ohm_1(P0)^#
    & [/\ ~~ ('C_K[x] \subset K'), 'N(<[x]>) \subset M & ~~ ('C[x] \subset L)]].
Proof.
have ntK: K :!=: 1%g := mmax_Fcore_neq1 maxM.
have nsKM: K <| M := Fcore_normal M.
have [sP0M pP0 _] := and3P sylP0.
have hallK: \pi(K).-Hall(M) K := Fcore_Hall M.
have K'p: p \notin \pi(K) by rewrite -p'groupEpi.
have K'P0: \pi(K)^'.-group P0 by rewrite (pi_pgroup pP0).
have [U hallU sP0U] := Hall_superset (mmax_sol maxM) sP0M K'P0.
have sylP0_U: p.-Sylow(U) P0 := pHall_subl sP0U (pHall_sub hallU) sylP0.
have{hallU} defM: K ><| U = M by apply/(sdprod_normal_p'HallP nsKM hallU).
have{K'P0} coKP0: coprime #|K| #|P0| by rewrite coprime_pi'.
have [/(_ _ _ sylP0_U)[abP0 rankP0] uCK _] := FTtypeI_II_facts maxM Mtype1 defM.
have{rankP0} /eqP prankP0: 'r_p(P0) == 2.
  by rewrite eqn_leq -{1}rank_pgroup // rankP0 (p_rank_Sylow sylP0).
have piP0p: p \in \pi(P0) by rewrite -p_rank_gt0 prankP0.
have [L maxL sP0Ls]: exists2 L, L \in 'M & P0 \subset L`_\s.
  have [DpiG _ _ _] := FT_Dade_support_partition gT.
  have:= piSg (subsetT P0) piP0p; rewrite DpiG => /exists_inP[L maxL piLs_p].
  have [_ /Hall_pi hallLs _] := FTcore_facts maxL.
  have [P sylP] := Sylow_exists p L`_\s; have [sPLs _] := andP sylP.
  have sylP_G: p.-Sylow(G) P := subHall_Sylow hallLs piLs_p sylP.
  have [y _ sP0_Py] := Sylow_subJ sylP_G (subsetT P0) pP0.
  by exists (L :^ y)%G; rewrite ?mmaxJ // FTcoreJ (subset_trans sP0_Py) ?conjSg.
split=> //; exists L => //; set P1 := 'Ohm_1(P0).
have abelP1: p.-abelem P1 := Ohm1_abelem pP0 abP0.
have [pP1 abP1 _] := and3P abelP1.
have sP10: P1 \subset P0 := Ohm_sub 1 P0; have sP1M := subset_trans sP10 sP0M.
have nKP1: P1 \subset 'N(K) by rewrite (subset_trans sP1M) ?gFnorm.
have nK'P1: P1 \subset 'N(K') := char_norm_trans (der_char 1 K) nKP1.
have{coKP0} coKP1: coprime #|K| #|P1| := coprimegS sP10 coKP0.
have solK: solvable K := nilpotent_sol (Fcore_nil M).
have isoP1: P1 \isog P1 / K'.
  by rewrite quotient_isog // coprime_TIg ?(coprimeSg (der_sub 1 K)).
have{ntK} ntKK': (K / K' != 1)%g.
  by rewrite -subG1 quotient_sub1 ?gFnorm ?proper_subn ?(sol_der1_proper solK).
have defKK': (<<\bigcup_(xbar in (P1 / K')^#) 'C_(K / K')[xbar]>> = K / K')%g.
  rewrite coprime_abelian_gen_cent1 ?coprime_morph ?quotient_norms //.
    by rewrite quotient_abelian.
  rewrite -(isog_cyclic isoP1) (abelem_cyclic abelP1).
  by rewrite -(p_rank_abelem abelP1) p_rank_Ohm1 prankP0.
have [xb P1xb ntCKxb]: {xb | xb \in (P1 / K')^# & 'C_(K / K')[xb] != 1}%g.
  apply/sig2W/exists_inP; rewrite -negb_forall_in.
  apply: contra ntKK' => /eqfun_inP regKP1bar.
  by rewrite -subG1 /= -defKK' gen_subG; apply/bigcupsP=> xb /regKP1bar->.
have [ntxb /morphimP[x nK'x P1x Dxb]] := setD1P P1xb.
have ntx: x != 1%g by apply: contraNneq ntxb => x1; rewrite Dxb x1 morph1.
have ntCKx: ~~ ('C_K[x] \subset K').
  rewrite -quotient_sub1 ?subIset ?gFnorm // -cent_cycle subG1 /=.
  have sXP1: <[x]> \subset P1 by rewrite cycle_subG.
  rewrite coprime_quotient_cent ?(coprimegS sXP1) ?(subset_trans sXP1) ?gFsub//.
  by rewrite quotient_cycle ?(subsetP nK'P1) // -Dxb cent_cycle.
have{uCK} UCx: 'M('C[x]) = [set M].
  rewrite -cent_set1 uCK -?card_gt0 ?cards1 // ?sub1set ?cent_set1.
    by rewrite !inE ntx (subsetP sP0U) ?(subsetP sP10).
  by apply: contraNneq ntCKx => ->; rewrite sub1G.
exists x; [by rewrite !inE ntx | split=> //].
  rewrite (sub_uniq_mmax UCx) /= -?cent_cycle ?cent_sub //.
  rewrite mFT_norm_proper ?cycle_eq1 //.
  by rewrite mFT_sol_proper abelian_sol ?cycle_abelian.
apply: contraL (leqW (p_rankS p sP0Ls)) => /(eq_uniq_mmax UCx)-> //.
by rewrite prankP0 /M`_\s (eqP Mtype1) /= ltnS p_rank_gt0.
Qed.

Variables (L : {group gT}) (x : gT).
Hypotheses (abP0 : abelian P0) (prankP0 : 'r_p(P0) = 2).
Hypotheses (maxL : L \in 'M) (sP0_Ls : P0 \subset L`_\s).
Hypotheses (P0_1s_x : x \in 'Ohm_1(P0)^#) (not_sCxK' : ~~ ('C_K[x] \subset K')).
Hypotheses (sNxM : 'N(<[x]>) \subset M) (not_sCxL : ~~ ('C[x] \subset L)).

Let H := L`_\F%G.

Let frobL : [Frobenius L with kernel H].
Proof.
have [sP0M pP0 _] := and3P sylP0.
have [ntx /(subsetP (Ohm_sub 1 _))P0x] := setD1P P0_1s_x.
have [Ltype1 | notLtype1] := boolP (FTtype L == 1)%N; last first.
  have [U W W1 W2 defW LtypeP] := FTtypeP_witness maxL notLtype1.
  suffices [Hx notLtype5]: x \in H /\ FTtype L != 5.
    have [_ _ _ tiFL] := compl_of_typeII_IV maxL LtypeP notLtype5.
    have Fx: x \in 'F(L)^# by rewrite !inE ntx (subsetP (Fcore_sub_Fitting L)).
    have /subsetP[y /cent1P cxy] := not_sCxL.
    have nzF: 'F(L)^# != set0 by apply/set0Pn; exists x.
    have{tiFL} /normedTI_memJ_P[//|tiFL _]: normedTI 'F(L)^# G L.
      apply/andP; rewrite normD1 setTI (mmax_normal maxL) ?gFnormal //.
      by rewrite trivg_Fitting ?mmax_sol ?mmax_neq1.
    by rewrite -(tiFL x) ?in_setT // /conjg -cxy mulKg.
  have [Ltype2 | notLtype2] := eqVneq (FTtype L) 2.
    by have:= sP0_Ls; rewrite /L`_\s Ltype2 => /subsetP->.
  have [_ _ [Ltype3 galL]] := FTtype34_structure maxL LtypeP notLtype2.
  have cycU: cyclic U.
    suffices regHU: Ptype_Fcompl_kernel LtypeP :=: 1%g.
      rewrite (isog_cyclic (quotient1_isog U)) -regHU.
      by have [|_ _ [//]] := typeP_Galois_P maxL _ galL; rewrite (eqP Ltype3).
    rewrite /Ptype_Fcompl_kernel unlock /= astabQ /=.
    have [_ _ ->] := FTtype34_Fcore_kernel_trivial maxL LtypeP notLtype2.
    rewrite -morphpreIim -injm_cent ?injmK ?ker_coset ?norms1 //.
    have [_ _ _ ->] := Mtype34_facts maxL LtypeP notLtype2.
    by apply/derG1P; have [] := compl_of_typeIII maxL LtypeP Ltype3.
  suffices sP0H: P0 \subset H by rewrite (eqP Ltype3) (subsetP sP0H).
  have sP0L': P0 \subset L^`(1) := subset_trans sP0_Ls (FTcore_sub_der1 maxL).
  have [_ [_ _ _ defL'] _ _ _] := LtypeP.
  have [nsHL' _ /mulG_sub[sHL' _] _ _] := sdprod_context defL'.
  have hallH := pHall_subl sHL' (der_sub 1 L) (Fcore_Hall L).
  have hallU: \pi(H)^'.-Hall(L^`(1)) U.
    by rewrite -(compl_pHall U hallH) sdprod_compl.
  rewrite (sub_normal_Hall hallH) // (pi_pgroup pP0) //.
  have: ~~ cyclic P0 by rewrite abelian_rank1_cyclic // (rank_pgroup pP0) prankP0.
  apply: contraR => piK'p.
  by have [y _ /cyclicS->] := Hall_psubJ hallU piK'p sP0L' pP0; rewrite ?cyclicJ.
have sP0H: P0 \subset H by have:= sP0_Ls; rewrite /L`_\s (eqP Ltype1).
have [U [LtypeF /= LtypeI]] := FTtypeP 1 maxL Ltype1.
have [[_ _ defL] _ _] := LtypeF; have [nsHL sUL _ nHU _] := sdprod_context defL.
have not_tiH: ~ trivIset (H^# :^: G).
  have H1x: x \in H^# by rewrite !inE ntx (subsetP sP0H).
  have nzH: H^# != set0 by apply/set0Pn; exists x.
  move=> tiH; have{tiH} /normedTI_memJ_P[//|tiH _]: normedTI H^# G L.
    by apply/andP; rewrite normD1 setTI (mmax_normal maxL) // -subG1 -setD_eq0.
  have /subsetP[y /cent1P cxy] := not_sCxL.
  by rewrite -(tiH x) ?in_setT // /conjg -cxy mulKg.
apply/existsP; exists U; have [_ -> _] := typeF_context LtypeF.
apply/forall_inP=> Q /SylowP[q pr_q sylQ]; have [sQU qQ _] := and3P sylQ.
rewrite (odd_pgroup_rank1_cyclic qQ) ?mFT_odd //.
apply: wlog_neg; rewrite -ltnNge => /ltnW; rewrite p_rank_gt0 => piQq.
have hallU: \pi(H)^'.-Hall(L) U.
  by rewrite -(compl_pHall U (Fcore_Hall L)) sdprod_compl.
have H'q := pnatPpi (pHall_pgroup hallU) (piSg sQU piQq).
rewrite leqNgt; apply: contra (H'q) => qrankQ; apply: IHp => //; last first.
  by rewrite (leq_trans qrankQ) ?p_rankS ?(subset_trans sQU).
have piHp: p \in \pi(H) by rewrite (piSg sP0H) // -p_rank_gt0 prankP0.
have pr_p: prime p by have:= piHp; rewrite mem_primes => /andP[].
have piUq: q \in \pi(exponent U) by rewrite pi_of_exponent (piSg sQU).
have [odd_p odd_q]: odd p /\ odd q.
  rewrite !odd_2'nat !pnatE //.
  by rewrite (pnatPpi _ piHp) ?(pnatPpi _ piQq) -?odd_2'nat ?mFT_odd.
have pgt2 := odd_prime_gt2 odd_p pr_p.
suffices [b dv_q_bp]: exists b : bool, q %| (b.*2 + p).-1.
  rewrite -ltn_double (@leq_ltn_trans (p + b.*2).-1) //; last first.
    by rewrite -!addnn -(subnKC pgt2) prednK // leq_add2l; case: (b).
  rewrite -(subnKC pgt2) dvdn_leq // -mul2n Gauss_dvd ?coprime2n //.
  by rewrite -{1}subn1 dvdn2 odd_sub // subnKC // odd_add odd_p odd_double addnC.
have [// | [cHH rankH] | [/(_ p piHp)Udvp1 _]] := LtypeI; last first.
  exists false; apply: dvdn_trans Udvp1.
  by have:= piUq; rewrite mem_primes => /and3P[].
suffices: q %| p ^ 2 - 1 ^ 2.
  rewrite subn_sqr addn1 subn1 Euclid_dvdM //.
  by case/orP; [exists false | exists true].
pose P := 'O_p(H); pose P1 := 'Ohm_1(P).
have chP1H: P1 \char H := char_trans (Ohm_char 1 _) (pcore_char p H).
have sylP: p.-Sylow(H) P := nilpotent_pcore_Hall p (Fcore_nil L).
have [sPH pP _] := and3P sylP.
have abelP1: p.-abelem P1 by rewrite Ohm1_abelem ?(abelianS sPH).
have [pP1 _] := andP abelP1.
have prankP1: 'r_p(P1) = 2.
  apply/eqP; rewrite p_rank_Ohm1 eqn_leq -{1}rank_pgroup // -{1}rankH rankS //=.
  by rewrite -prankP0 (p_rank_Sylow sylP) p_rankS //.
have ntP1: P1 != 1%g by rewrite -rank_gt0 (rank_pgroup pP1) prankP1.
have [_ _ [U0 [sU0U expU0 frobHU0]]] := LtypeF.
have nP1U0: U0 \subset 'N(P1).
  by rewrite (char_norm_trans chP1H) ?(subset_trans sU0U).
rewrite subn1 -prankP1 p_rank_abelem // -card_pgroup //.
have frobP1U0 := Frobenius_subl ntP1 (char_sub chP1H) nP1U0 frobHU0.
apply: dvdn_trans (Frobenius_dvd_ker1 frobP1U0).
by have:= piUq; rewrite -expU0 pi_of_exponent mem_primes => /and3P[].
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
have [[sPH pP _] [sP0M pP0 _]] := (and3P sylP, and3P sylP0). 
have sP0P: P0 \subset P by rewrite (sub_normal_Hall sylP) ?pcore_normal.
have defP0: P :&: M = P0.
  rewrite [P :&: M](sub_pHall sylP0 (pgroupS _ pP)) ?subsetIl ?subsetIr //.
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
    exact: FTtype1_seqInd_ortho.
  rewrite inE -/K (contra _ ntx) // => Kx.
  rewrite -(consttC p x) !(constt1P _) ?mulg1 ?(mem_p_elt p'K) //.
  by rewrite p_eltNK (mem_p_elt (pHall_pgroup sylP0)).
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

Let rhoM := (invDade (FT_Dade1_hyp maxM)).

Let rhoM_psi :
  [/\ {in K^#, rhoM psi =1 psi},
      {in K :\: K' &, forall g1 g2, psi g1 = psi g2}
    & {in K :\: K', forall g, psi g \in Cint}].
Proof.
have [nsKM nsHL]: K <| M /\ H <| L by rewrite !gFnormal.
have pr_p: prime p.
  by have:= ltnW prankM; rewrite p_rank_gt0 mem_primes => /andP[].
have [sP0M pP0 _] := and3P sylP0; have abelP01 := Ohm1_abelem pP0 abP0.
have not_frobM: ~~ [Frobenius M with kernel K].
  apply: contraL prankM => /(set_Frobenius_compl defM)frobM.
  rewrite -leqNgt -(p_rank_Sylow sylP0) -p_rank_Ohm1 p_rank_abelem //.
  rewrite -abelem_cyclic // (cyclicS (Ohm_sub _ _)) //.
  have sP0ML: P0 \subset M :&: L.
    by rewrite subsetI sP0M (subset_trans sP0H) ?gFsub.
  rewrite nil_Zgroup_cyclic ?(pgroup_nil pP0) // (ZgroupS sP0ML) //.
  have [U [MtypeF _]] := FTtypeP 1 maxM Mtype1.
  by have{MtypeF} /typeF_context[_ <- _] := compl_of_typeF defM MtypeF.
pose rmR := sval (Rgen maxL Ltype1).
have Zpsi: psi \in 'Z[rmR chi].
  case: (Rgen _ _) @rmR => /= rmR []; rewrite -/calS => scohS _ _.
  have sSS: cfConjC_subset calS calS by apply: seqInd_conjC_subset1.
  have [B /mem_subseq sBR Dpsi] := mem_coherent_sum_subseq scohS sSS cohS Schi.
  by rewrite [psi]Dpsi big_seq rpred_sum // => xi /sBR/mem_zchar->.
have part1: {in K^#, rhoM psi =1 psi}.
  move=> g K1g; rewrite /= cfunElock.
  rewrite def_FTsignalizer1 ?(subsetP (Fcore_sub_FTsupp1 _)) // /'R_M.
  case: ifPn => [_ | sCg'M]; first by rewrite cards1 big_set1 invr1 mul1r mul1g.
  have Dg: g \in [set z in 'A0(M) | ~~ ('C[z] \subset M)].
    by rewrite inE (subsetP (Fcore_sub_FTsupp0 _)).
  have [_ [_ /(_ g Dg)maxN] /(_ g Dg)[_ _ ANg Ntype12]] := FTsupport_facts maxM.
  have{maxN} [maxN sCgN] := mem_uniq_mmax maxN.
  have{Ntype12} Ntype1: FTtype 'N[g] == 1%N.
    have [] := Ntype12; rewrite -(mem_iota 1 2) !inE => /orP[// | Ntype2] frobM.
    by have /negP[] := not_frobM; apply/frobM/Ntype2.
  have not_frobN: ~~ [Frobenius 'N[g] with kernel 'N[g]`_\F].
    apply/Frobenius_kerP=> [[_ _ _ regFN]].
    have [/bigcupP[y]] := setDP ANg; rewrite /'A1(_) /_`_\s (eqP Ntype1) /=.
    by move=> /regFN sCyF /setD1P[ntg cNy_g]; rewrite 2!inE ntg (subsetP sCyF).
  have LG'N: gval 'N[g] \notin L :^: G.
    apply: contra not_frobN => /imsetP[y _ ->]; rewrite FcoreJ.
    apply: FrobeniusWker (E :^ y)%G _ _; apply: FrobeniusJ.
    exact: set_Frobenius_compl defL frobL.
  suff /(eq_bigr _)->: {in 'C_('N[g]`_\F)[g], forall z, psi (z * g)%g = psi g}.
    by rewrite sumr_const -[psi g *+ _]mulr_natl mulKf ?neq0CG.
  move=> z /setIP[Fz /cent1P cgz].
  have{Fz cgz}: (z * g \in g *: 'N[g]`_\F)%g by rewrite cgz mem_lcoset mulKg.
  apply: FTtype1_ortho_constant => [phi calMphi|].
    apply/orthoPl=> nu /memv_span; apply: span_orthogonal (zchar_span Zpsi).
    exact: FTtype1_seqInd_ortho.
  have [/(subsetP (FTsupp_sub _))/setD1P[ntg Ng]] := setDP ANg.
  by rewrite /'A1(_) /_`_\s (eqP Ntype1) /= !inE ntg Ng andbT.
have part2: {in K :\: K' &, forall g1 g2 : gT, psi g1 = psi g2}.
  pose rho := invDade (FT_Dade_hyp maxM).
  have eq_rho: {in K :\: K', rho psi =1 psi}.
    move=> g /setDP[Kg /group1_contra ntg].
    have K1g: g \in K^# by rewrite !inE ntg.
    have [sK1A1 sK1A] := (Fcore_sub_FTsupp1 maxM, Fcore_sub_FTsupp maxM).
    rewrite -part1 // !cfunElock def_FTsignalizer ?(subsetP sK1A) //.
    by rewrite def_FTsignalizer1 ?(subsetP sK1A1).
  have LG'M: gval M \notin L :^: G.
    apply: contra not_frobM => /imsetP[y _ /= ->]; rewrite FcoreJ.
    apply: FrobeniusWker (E :^ y)%G _ _; apply: FrobeniusJ.
    exact: set_Frobenius_compl defL frobL.
  move=> g1 g2 Kg1 Kg2; rewrite /= -!eq_rho //.
  apply: FtypeI_invDade_ortho_constant => // phi calMphi.
  apply/orthoPl=> nu /memv_span; apply: span_orthogonal (zchar_span Zpsi).
  exact: FTtype1_seqInd_ortho.
split=> // g KK'g; pose nKK' : algC := #|K :\: K'|%:R.
pose nK : algC := #|K|%:R; pose nK' : algC := #|K'|%:R.
have nzKK': nKK' != 0 by rewrite pnatr_eq0 cards_eq0; apply/set0Pn; exists g.
have Dpsi_g: nK * '['Res[K] psi, 1] = nK' * '['Res[K'] psi, 1] + nKK' * psi g.
  rewrite !mulVKf ?neq0CG // (big_setID K') (setIidPr (gFsub _ _)) /=.
  rewrite mulr_natl -sumr_const; congr (_ + _); apply: eq_bigr => z K'z.
    by rewrite !cfun1E !cfResE ?subsetT ?(subsetP (der_sub 1 K)) ?K'z.
  have [Kz _] := setDP K'z; rewrite cfun1E Kz conjC1 mulr1 cfResE ?subsetT //.
  exact: part2.
have{Zpsi} Zpsi: psi \in 'Z[irr G] by have [[_ ->//]] := cohS; apply: mem_zchar.
have Qpsi1 R: '['Res[R] psi, 1] \in Crat.
  by rewrite rpred_Cint ?Cint_cfdot_vchar ?rpred1 ?cfRes_vchar.
apply: Cint_rat_Aint (Aint_vchar g Zpsi).
rewrite -[psi g](mulKf nzKK') -(canLR (addKr _) Dpsi_g) addrC mulrC.
by rewrite rpred_div ?rpredB 1?rpredM ?rpred_nat ?Qpsi1.
Qed.

(* This is the main part of Peterfalvi (12.16). *)
Lemma FTtype1_nonFrobenius_witness_contradiction : False.
Proof.
have pr_p: prime p.
  by have:= ltnW prankM; rewrite p_rank_gt0 mem_primes => /andP[].
have [sP0M pP0 _] := and3P sylP0; have abelP01 := Ohm1_abelem pP0 abP0.
have [ntx P01x] := setD1P P0_1s_x.
have ox: #[x] = p := abelem_order_p abelP01 P01x ntx.
have odd_p: odd p by rewrite -ox mFT_odd.
have pgt2 := odd_prime_gt2 odd_p pr_p.
have Zpsi: psi \in 'Z[irr G] by have [[_ ->//]] := cohS; apply: mem_zchar.
have lb_psiM: '[rhoM psi] >= #|K :\: K'|%:R / #|M|%:R * e.-1%:R ^+ 2.
  have [g /setIP[Kg cxg] notK'g] := subsetPn not_sCxK'.
  have KK'g: g \in K :\: K' by rewrite !inE notK'g.
  have [rhoMid /(_ _ g _ KK'g)psiKK'_id /(_ g KK'g)Zpsig] := rhoM_psi.
  rewrite -mulrA mulrCA ler_pmul2l ?invr_gt0 ?gt0CG // mulr_natl.
  rewrite (big_setID (K :\: K')) (setIidPr _) ?subDset ?subsetU ?gFsub ?orbT //.
  rewrite ler_paddr ?sumr_ge0 // => [z _|]; first exact: mul_conjC_ge0.
  rewrite -sumr_const ler_sum // => z KK'z.
  rewrite {}rhoMid ?(subsetP _ z KK'z) ?setDS ?sub1G // {}psiKK'_id {z KK'z}//.
  rewrite -normCK ler_sqr ?qualifE ?ler0n ?normr_ge0 //.
  have [eps prim_eps] := C_prim_root_exists (prime_gt0 pr_p).
  have psi_xg: (psi (x * g)%g == e%:R %[mod 1 - eps])%A.
    have [-> // _] := rhoL_psi; rewrite -[x]mulg1 -chi1.
    rewrite (vchar_ker_mod_prim prim_eps) ?group1 ?(seqInd_vcharW Schi) //.
    rewrite (subsetP _ _ P01x) // (subset_trans (Ohm_sub 1 _)) //.
    by rewrite (subset_trans sP0H) ?gFsub.
  have{psi_xg} /dvdCP[a Za /(canRL (subrK _))->]: (p %| psi g - e%:R)%C.
    rewrite (int_eqAmod_prime_prim prim_eps) ?rpredB ?rpred_nat // eqAmod0.
    apply: eqAmod_trans psi_xg; rewrite eqAmod_sym.
    by rewrite (vchar_ker_mod_prim prim_eps) ?in_setT.
  have [-> | nz_a] := eqVneq a 0.
    by rewrite mul0r add0r normr_nat leC_nat leq_pred.
  rewrite -[e%:R]opprK (ler_trans _ (ler_sub_dist _ _)) // normrN normrM.
  rewrite ler_subr_addl !normr_nat -natrD.
  apply: ler_trans (_ : 1 * p%:R <= _); last first.
    by rewrite ler_wpmul2r ?ler0n ?norm_Cint_ge1.
  rewrite mul1r leC_nat -subn1 addnBA ?cardG_gt0 // leq_subLR addnn -muln2.
  have [b e_dv_pb]: exists b : bool, e %| (b.*2 + p).-1.
    by have [_ /orP[]] := Ecyclic_le_p; [exists false | exists true].
  apply: (@leq_trans (b.*2 + p).-1); last first.
    by case: {e_dv_pb}b => //=; rewrite -subn1 leq_subLR !leqW.
  apply: dvdn_leq; first by rewrite -(subnKC pgt2) !addnS.
  rewrite Gauss_dvd ?coprimen2 ?mFT_odd // e_dv_pb dvdn2 -subn1.
  by rewrite -addnBA ?odd_add ?odd_sub ?prime_gt0 // odd_double odd_p.
have irrS: {subset calS <= irr L} by have [] := FT_Frobenius_coherence maxL.
have defAL: 'A(L) = H^#.
  apply/eqP; rewrite eqEsubset Fcore_sub_FTsupp // andbT.
  apply/bigcupsP=> y; rewrite /'A1(L) /L`_\s (eqP Ltype1) /= => H1y.
  by rewrite setSD //; have [_ _ _ ->] := Frobenius_kerP frobL.
have lb_psiL: '[rhoL psi] >= 1 - e%:R / #|H|%:R.
  (* crudely lifted from (12.14)... *)
  have nsHL: H <| L by rewrite gFnormal.
  have nH1L: L \subset 'N(H^#) by rewrite normD1 gFnorm.
  pose ddLH := restr_Dade_hyp (FT_Dade_hyp maxL) (Fcore_sub_FTsupp maxL) nH1L.
  have ->: rhoL psi = invDade ddLH psi.
    by apply/cfunP=> y; rewrite !cfunElock /Dade_signalizer defAL.
  have cohS_H: coherent_with calS H^# (Dade ddLH) tau1.
    have [IZtau Dtau] := cohS; split=> // xi Hxi.
    by rewrite [Dade _ _]restr_DadeE ?(zchar_on Hxi) ?Dtau ?zcharD1_seqInd.
  have /irrP[t Dchi] := irrS _ Schi; have St: 'chi_t \in calS by rewrite -Dchi.
  have Sgt1: (1 < size calS)%N by apply: seqInd_nontrivial St; rewrite ?mFT_odd.
  have De: #|L : H| = e by rewrite -(index_sdprod defL).
  have:= Dade_Ind1_sub_lin cohS_H Sgt1 St; rewrite -Dchi -/calS -/psi /=.
  rewrite De => [[]] // _ [_ _ []//].
  rewrite ler_pdivl_mulr ?ltr0n // -natrM -(natrB _ (cardG_gt0 H)) leC_nat.
  rewrite dvdn_leq ?subn_gt0 ?cardG_gt1 ?mmax_Fcore_neq1 // mulnC.
  rewrite Gauss_dvd ?coprime2n ?mFT_odd // dvdn2 odd_sub ?cardG_gt0 // mFT_odd.
  by rewrite /= -De subn1 Frobenius_ker_dvd_ker1.
have not_LGM: gval M \notin L :^: G.
  apply: contraL p'K => /= /imsetP[z _ ->]; rewrite FcoreJ pgroupJ.
  by rewrite p'groupEpi (piSg sP0H) // -p_rank_gt0 prankP0.
have{not_LGM} tiA1_LM: [disjoint 'A1~(L) & 'A1~(M)].
  (* going the long route, via (8.17) -- (8.18)(c) would be much more direct. *)
  have [_ _ _] := FT_Dade_support_partition gT.
  set PG := _ @: _ => [[injA1 partPG partPG_W]].
  have tiPG: trivIset PG.
    have [/forall_inP|[S [T [_ W W1 W2 defW]]]] := FTtypeP_pair_cases gT.
      by case/partPG/and3P.
    case/partPG_W=> /and3P[_ tiPGW _] _.
    apply/trivIsetP=> AM1 AM2 PG_AM1 PG_AM2.
    by apply: (trivIsetP tiPGW); rewrite ?inE ?PG_AM1 ?PG_AM2 ?orbT.
  have [_ _ _ ontoMG] := mmax_transversalP gT.
  have [[y MG_Ly] [z MG_Mz]] := (ontoMG L maxL, ontoMG M maxM).
  rewrite -(FT_Dade1_supportJ L y) -(FT_Dade1_supportJ M z).
  apply: (trivIsetP tiPG); do ?apply: mem_imset => //.
  rewrite (inj_in_eq injA1) // -val_eqE /=; apply: contraNneq not_LGM.
  by rewrite -(orbit_actr _ _ _ (in_setT z)) /= => <-; rewrite mem_orbit.
have{tiA1_LM} ub_rhoML: '[rhoM psi] + '[rhoL psi] < 1.
  have [[Itau1 Ztau1] _] := cohS.
  have n1psi: '[psi] = 1 by rewrite Itau1 ?mem_zchar ?irrWnorm ?irrS.
  rewrite -n1psi (cfnormE (cfun_onG psi)) (big_setD1 1%g) ?group1 //=.
  rewrite mulrDr ltr_spaddl 1?mulr_gt0 ?invr_gt0 ?gt0CG ?exprn_gt0 //.
    have /dirrP[s [i ->]]: psi \in dirr G.
      by rewrite dirrE Ztau1 ?mem_zchar ?n1psi /=.
    by rewrite cfunE normrMsign normr_gt0 irr1_neq0.
  rewrite (big_setID 'A1~(M)) mulrDr ler_add //=.
    rewrite -FT_Dade1_supportE (setIidPr _) ?Dade_support_subD1 //.
    exact: leC_cfnorm_invDade_support.
  rewrite (big_setID 'A1~(L)) mulrDr ler_paddr //=.
    rewrite mulr_ge0 ?invr_ge0 ?ler0n ?sumr_ge0 // => z _.
    by rewrite exprn_ge0 ?normr_ge0.
  rewrite (setIidPr _); last first.
    by rewrite subsetD tiA1_LM -FT_Dade1_supportE Dade_support_subD1.
  have ->: rhoL psi = invDade (FT_Dade1_hyp maxL) psi.
    apply/cfunP=> y; rewrite !cfunElock /Dade_signalizer defAL.
    by rewrite /'A1(L) /L`_\s (eqP Ltype1).
  by rewrite -FT_Dade1_supportE leC_cfnorm_invDade_support.
have ubM: (#|M| <= #|K| * #|H|)%N.
  by rewrite -(sdprod_card defM) leq_mul // subset_leq_card.
have{lb_psiM lb_psiL ub_rhoML ubM} ubK: (#|K / K'|%g < 4)%N.
  rewrite card_quotient ?gFnorm -?ltC_nat //.
  rewrite -ltf_pinv ?qualifE ?gt0CiG ?ltr0n // natf_indexg ?gFsub //.
  rewrite invfM invrK mulrC -(subrK #|K|%:R #|K'|%:R) mulrDl divff ?neq0CG //.
  rewrite -opprB mulNr addrC ltr_subr_addl -ltr_subr_addr.
  have /Frobenius_context[_ _ ntE _ _] := set_Frobenius_compl defL frobL.
  have egt2: (2 < e)%N by rewrite odd_geq ?mFT_odd ?cardG_gt1. 
  have e1_gt0: 0 < e.-1%:R :> algC by rewrite ltr0n -(subnKC egt2).
  apply: ltr_le_trans (_ : e%:R / e.-1%:R ^+ 2 <= _).
    rewrite ltr_pdivl_mulr ?exprn_gt0 //.
    rewrite -(@ltr_pmul2r _ #|H|%:R^-1) ?invr_gt0 ?gt0CG // mulrAC.
    rewrite -(ltr_add2r 1) -ltr_subl_addl -addrA.
    apply: ler_lt_trans ub_rhoML; rewrite ler_add //.
    apply: ler_trans lb_psiM; rewrite -natrX ler_wpmul2r ?ler0n //.
    rewrite cardsD (setIidPr _) ?gFsub // -natrB ?subset_leq_card ?gFsub //.
    rewrite -mulrA ler_wpmul2l ?ler0n //.
    rewrite ler_pdivr_mulr ?gt0CG // ler_pdivl_mull ?gt0CG //.
    by rewrite ler_pdivr_mulr ?gt0CG // mulrC -natrM leC_nat.
  rewrite -(ler_pmul2l (gt0CG E)) -/e mulrA -expr2 invfM -exprMn.
  apply: ler_trans (_ : (1 + 2%:R^-1) ^+ 2 <= _).
    rewrite ler_sqr ?rpred_div ?rpredD ?rpred1 ?rpredV ?rpred_nat //.
    rewrite -{1}(ltn_predK egt2) mulrSr mulrDl divff ?gtr_eqF // ler_add2l.
    rewrite ler_pdivr_mulr // ler_pdivl_mull ?ltr0n //.
    by rewrite mulr1 leC_nat -(subnKC egt2).
  rewrite -(@ler_pmul2r _ (2 ^ 2)%:R) ?ltr0n // {1}natrX -exprMn -mulrA.
  rewrite mulrDl mulrBl !mul1r !mulVf ?pnatr_eq0 // (mulrSr _ 3) addrK.
  by rewrite -mulrSr ler_wpmul2r ?ler0n ?ler_nat.
have [U [MtypeF _]] := FTtypeP 1 maxM Mtype1.
have{U MtypeF} [_ _ [U0 [sU0ML expU0 frobU0]]] := compl_of_typeF defM MtypeF.
have [/sdprodP[_ _ nKU0 tiKU0] ntK _ _ _] := Frobenius_context frobU0.
have nK'U0: U0 \subset 'N(K') := char_norm_trans (der_char 1 K) nKU0.
have frobU0K': [Frobenius K <*> U0 / K' = (K / K') ><| (U0 / K')]%g.
  have solK: solvable K by rewrite ?nilpotent_sol ?Fcore_nil.
  rewrite  Frobenius_proper_quotient ?(sol_der1_proper solK) // /(_ <| _).
  by rewrite (subset_trans (der_sub 1 _)) ?joing_subl // join_subG gFnorm.
have isoU0: U0 \isog U0 / K'.
  by rewrite quotient_isog //; apply/trivgP; rewrite -tiKU0 setSI ?gFsub.
have piU0p: p \in \pi(U0 / K')%g.
  rewrite /= -(card_isog isoU0) -pi_of_exponent expU0 pi_of_exponent.
  rewrite mem_primes pr_p cardG_gt0 /= -ox order_dvdG // (subsetP _ _ P01x) //.
  rewrite (subset_trans (Ohm_sub 1 _)) // subsetI sP0M.
  by rewrite (subset_trans sP0H) ?gFsub.
have /(Cauchy pr_p)[z U0z oz]: p %| #|U0 / K'|%g.
  by rewrite mem_primes in piU0p; case/and3P: piU0p.
have frobKz: [Frobenius (K / K') <*> <[z]> = (K / K') ><| <[z]>]%g.
  rewrite (Frobenius_subr _ _ frobU0K') ?cycle_subG //.
  by rewrite cycle_eq1 -order_gt1 oz ltnW.
have: p %| #|K / K'|%g.-1 by rewrite -oz (Frobenius_dvd_ker1 frobKz) //.
have [_ ntKK' _ _ _] := Frobenius_context frobKz.
rewrite -subn1 gtnNdvd ?subn_gt0 ?cardG_gt1 // subn1 prednK ?cardG_gt0 //.
by rewrite -ltnS (leq_trans ubK).
Qed.

End Twelve_13_to_16.

Lemma FTtype1_nonFrobenius_contradiction : False.
Proof.
have [_ [tau1 cohS]] := FT_Frobenius_coherence maxL frobL.
have [ntH _ nsHL _] := Frobenius_kerP frobL.
have solH: solvable H by rewrite nilpotent_sol ?Fcore_nil.
have [s lin_s nt_s] := solvable_has_lin_char ntH solH.
pose chi := 'Ind[L] 'chi_s.
have Schi: chi \in calS.
  by rewrite mem_seqInd ?normal1 // !inE sub1G subGcfker -irr_eq1 nt_s.
have chi1: chi 1%g = e%:R.
  by rewrite cfInd1 ?gFsub // -(index_sdprod defL) lin_char1 ?mulr1.
exact: FTtype1_nonFrobenius_witness_contradiction cohS Schi chi1.
Qed.

End Twelve_8_to_16.

(* This is Peterfalvi, Theorem (12.7). *)
Theorem FTtype1_Frobenius M :
  M \in 'M -> FTtype M == 1%N -> [Frobenius M with kernel M`_\F].
Proof.
set K := M`_\F => maxM Mtype1; have [U [MtypeF _]] := FTtypeP 1 maxM Mtype1.
have hallU: \pi(K)^'.-Hall(M) U.
  by rewrite -(compl_pHall U (Fcore_Hall M)) sdprod_compl; have [[]] := MtypeF.
apply: FrobeniusWker (U) _ _; have{MtypeF} [_ -> _] := typeF_context MtypeF.
apply/forall_inP=> P0 /SylowP[p _ sylP0].
rewrite (odd_pgroup_rank1_cyclic (pHall_pgroup sylP0)) ?mFT_odd // leqNgt.
apply/negP=> prankP0.
have piUp: p \in \pi(U) by rewrite -p_rank_gt0 -(p_rank_Sylow sylP0) ltnW.
have{piUp} K'p: p \in \pi(K)^' := pnatPpi (pHall_pgroup hallU) piUp.
have{U hallU sylP0} sylP0: p.-Sylow(M) P0 := subHall_Sylow hallU K'p sylP0.
have{P0 sylP0 prankP0} prankM: (1 < 'r_p(M))%N by rewrite -(p_rank_Sylow sylP0).
case/negP: K'p => /=.
elim: {p}_.+1 {-2}p M @K (ltnSn p) maxM Mtype1 prankM => // p IHp q M K.
rewrite ltnS leq_eqVlt => /predU1P[->{q} | /(IHp q M)//] maxM Mtype1 prankM.
apply/idPn; rewrite -p'groupEpi /= -/K => p'K.
have [P0 sylP0] := Sylow_exists p M.
have [] := non_Frobenius_FTtype1_witness maxM Mtype1 prankM p'K sylP0.
move=> abP0 prankP0 [L [maxL sP0_Ls [x P01s_x []]]].
exact: (FTtype1_nonFrobenius_contradiction IHp) P01s_x. 
Qed.

(* This will be (12.17). *)
Theorem not_all_FTtype1 : ~~ all_FTtype1 gT.
Admitted.


End PFTwelve.
