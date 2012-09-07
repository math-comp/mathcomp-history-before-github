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
Let tau := FT_Dade0 maxL.

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
      {in S_ chi, forall i, 'chi_i \in 'CF(L, 'A(L) :|: 1%G)}].
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
have defT: H ><| 'I_U['chi_t] = T.
  have := sdprod_modl sdHU sHT.
  rewrite {1}(setIidPr sTL).
    (* should be a lemma in inertia: *)
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
  suff : ~~ (H \subset cfker 'chi_j) by move/(not_in_ker_char0 _ _); apply.
  suff : j \in Iirr_kerD L H 1%G by rewrite /Iirr_kerD !inE sub1G andbT.
  by apply/S_calSP; exists chi.
Qed.

(* This is Peterfalvi (12.2a), second part *)
Lemma tau_isometry  : {in 'Z[calI, L^#], isometry tau, to 'Z[irr G, G^#]}.
Proof.
apply: (sub_iso_to _ _ (Dade_Zisometry _)) => //.
have /subsetD1P[_ /setU1K <-] := FTsupp0_sub L.
move=> phi; rewrite zcharD1E FTsupp0_type1 // => /andP[S_phi phi1nz].
rewrite zcharD1 {}phi1nz andbT setUC.
apply: zchar_trans_on phi S_phi => ? /imageP[i /S_calSP[j calSj Sj_i] ->].
rewrite zchar_split irr_vchar /=.
by have [_ _ ->] := PF_12_2a calSj.
Qed.

Lemma mem_flatten_im_in (F : finType)(T : eqType)(f : F -> seq T) (P : pred F) (x : T) :
    x \in flatten [seq f x | x in P] -> exists2 i, i \in P & x \in f i.
have: all P (enum P) by apply/allP=> x1; rewrite mem_enum.
rewrite /(image _ _); elim: (enum P) => //= a l ih /andP[Pa hall]. 
by rewrite mem_cat; case/orP=> hx; [exists a | apply: ih].
Qed.

Lemma mem_flatten_im (F : finType)(T : eqType)(f : F -> seq T) l (x : T) :
    x \in flatten [seq f x | x <- l] -> exists2 i, i \in l & x \in f i.
rewrite /(image _ _); elim: l => //= a l ih.
rewrite mem_cat; case/orP=> hx; first by exists a; rewrite // mem_head.
case: (ih hx) => b lb xfb; exists b => //; exact: mem_behead.
Qed.

Lemma FPtype1_Iirr_kerD_subcoherent : 
 {R : 'CF(L) -> seq _ |  subcoherent calI tau R}.
Proof.
apply: irr_subcoherent; last exact: tau_isometry.
split. 
- by apply/dinjectiveP; apply: in2W irr_inj.
- move=> _ /imageP[i _ ->]; exact: mem_irr.
- move=> psi /imageP[i /S_calSP[phi calSphi]]; rewrite inE => irri -> {psi}.
  rewrite -conjC_IirrE; apply: chi_calI; apply/S_calSP.
  exists (phi^*)%CF; first by rewrite ?cfAut_seqInd.
  by rewrite inE irr_consttE conjC_IirrE cfdot_conjC conjC_eq0 -irr_consttE.
- apply/hasPn=> psi; case/imageP => i /S_calSP[phi calSphi].
  rewrite inE => irri -> {psi}; rewrite /cfReal odd_eq_conj_irr1 ?mFT_odd //.
  rewrite  irr_eq1; case/seqIndC1P: (calSphi)=> k kn0 phiE. 
  apply: contra kn0 => /eqP j0;  move: irri; rewrite j0 phiE.
  by rewrite constt_Ind_constt_Res irr0 cfRes_cfun1 -irr0 constt_irr inE.
Qed.

Lemma irr_constt_ortho (gT' : finGroupType) (A : {group gT'}) (phi psi : 'CF(A)) i j : 
  phi \is a character -> psi \is a character -> orthogonal phi psi -> 
  i \in irr_constt phi -> j \in irr_constt psi -> orthogonal 'chi_i 'chi_j.
Proof.
move=> char_phi char_psi /orthoP /eqP ophi_psi irr_i irr_j; apply/orthoP.
rewrite cfdot_irr; apply/eqP; move/charf0P: Cchar->; rewrite eqb0; move: ophi_psi.
apply: contraL => /eqP ijD.
case/(constt_charP _ char_phi) : irr_i => phi1 phi1_char ->.
case/(constt_charP _ char_psi) : irr_j => psi1 psi1_char ->.
rewrite cfdotDl cfdotDr ijD cfnorm_irr.
have /truncCK <- : '['chi_j, psi1] \in Cnat.
  by rewrite cfdotC Cnat_aut Cnat_cfdot_char_irr.
have /truncCK <- : '[phi1, 'chi_j + psi1] \in Cnat.
  by rewrite Cnat_cfdot_char // rpredD ?irr_char.
by rewrite -[1]/(1%:R) -!natrD; move/charf0P: Cchar->.
Qed.

(* This is Peterfalvi (12.2)(b) *)
Lemma FPtype1_calS_subcoherent :
  {R : 'CF(L) -> seq _ | let R1 := sval FPtype1_Iirr_kerD_subcoherent in
    [/\ subcoherent calS tau R,
      forall i (phi := 'chi_i),
      i \in Iirr_kerD L H 1%G -> 
      [/\ orthonormal (R1 phi),
          size (R1 phi) = 2 &
          (tau (phi - phi^*%CF) = (\sum_(mu <- R1 phi) mu)%CF)] &
      forall chi, chi \in calS ->
        R chi = flatten [seq (R1 'chi_i) | i in S_ chi]]
}.
Proof.
have nHL : H <| L by exact: gFnormal.
have nrS : ~~ has cfReal calS by apply: seqInd_notReal; rewrite ?mFT_odd.
have U_S : uniq calS by exact: seqInd_uniq.
have ccS : conjC_closed calS by exact:cfAut_seqInd.
have conjCS : cfConjC_subset calS (seqIndD H L H 1) by split.
case: FPtype1_Iirr_kerD_subcoherent => R1 subc1. 
case: (subc1) => [[chi_char nrI ccI] tau_iso oI h1 hortho].
pose R chi := flatten [seq R1 'chi_i | i in S_ chi].
have aux phi psi iphi ipsi Rphi Rpsi : phi \in calS -> psi \in calS ->
  iphi \in S_ phi -> ipsi \in S_ psi -> 
  Rphi \in R1 'chi_ iphi -> Rpsi \in R1 'chi_ipsi -> 
  orthogonal 'chi_iphi ('chi_ipsi :: ('chi_ipsi)^*%CF) -> '[Rphi, Rpsi] = 0.
  move=> calS_phi calS_psi; rewrite ![_ \in S_ _]inE =>  Scphi Scpsi.
  move=> Rphi_in Rpsi_in /= ochi.
  have calI_iphi : 'chi_iphi \in calI.
    rewrite /calI; apply: map_f; rewrite mem_enum; apply/S_calSP; exists phi => //.
    by rewrite inE.
  have calI_ipsi : 'chi_ipsi \in calI.
    rewrite /calI; apply: map_f; rewrite mem_enum; apply/S_calSP; exists psi => //.
    by rewrite inE.
    by have /orthogonalP -> := (hortho _ _ calI_ipsi calI_iphi ochi).
exists R; split => //= => [| i Ii]; last first.
  have mem_i := (chi_calI Ii); have [Zirr oR1 tau_im] := (h1  _ mem_i).
  split=> // {h1}; move/(f_equal (fun x : 'CF([set: gT]%G) => '[ x ])): tau_im.
  rewrite cfnorm_orthonormal //.
  have hsubchi : 'chi_i - (('chi_i)^*)%CF \in 'Z[calI, L^#].
    - have hchi : 'chi_i \in 'Z[calI, L] by rewrite mem_zchar_on // cfun_onG.
    rewrite sub_aut_zchar ?cfAut_zchar // => ? /imageP[j _ ->]; exact: irr_vchar.
  case: tau_iso => h1 _; rewrite {}h1 // {hsubchi} cfnormBd => [/eqP|]; last first.
    case/pairwise_orthogonalP: oI => _ -> //; rewrite ?ccI //.
    by move/hasPn: nrI => /(_ _ mem_i); rewrite eq_sym.
  by rewrite cfnorm_conjC cfnorm_irr -[1]/(1%:R) -natrD eqC_nat; move/eqP<-.
have calS_portho : pairwise_orthogonal calS by exact: seqInd_orthogonal.
have calS_char : {subset calS <= character} by apply: seqInd_char.
have calS_chi_ortho : {in calS &, forall (phi psi : 'CF(_)) i j, 
  orthogonal phi psi -> 
  i \in irr_constt phi -> j \in irr_constt psi -> orthogonal 'chi_i 'chi_j}.
  by move=> ? ? ? ? /= ? ?; apply: irr_constt_ortho; apply/calS_char.
split => //.
- apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
  have /subsetD1P[_ /setU1K <-] := FTsupp0_sub L.
  rewrite zcharD1E FTsupp0_type1 // => /andP[S_phi phi1nz].
  rewrite zcharD1 {}phi1nz andbT setUC.
  apply: zchar_trans_on phi S_phi => psi calS_psi.
  rewrite zchar_split (seqInd_vcharW calS_psi) /=.
  by have [{3}-> _ hCF] := PF_12_2a calS_psi; rewrite rpred_sum. 
- move=> phi calS_phi; case/PF_12_2a: (calS_phi)=> {1}-> _ _.
  have tau_Rphi: {subset R phi <= 'Z[irr [set: gT]%G]}.
    move=> psi /mem_flatten_im_in [iphi Scphi Rpsi_in].
    suff calI_iphi : 'chi_iphi \in calI.
    - by case: (h1 _ calI_iphi) => subZ _ _; apply: subZ.
    by apply/chi_calI/S_calSP; exists phi => //; case: (PF_12_2a calS_phi)=> ->.
  suff h : orthonormal (R phi) /\
           tau (phi - (phi^*)%CF) = \sum_(alpha <- R phi) alpha.
    by split; case: h.
  have [phiD hdeg _] := PF_12_2a calS_phi.
  have {phiD} phiD :  phi = \sum_(i <- enum (S_ phi)) 'chi_i.
    rewrite {1}phiD.
    by rewrite big_uniq /= ?enum_uniq //; apply: eq_bigl => x; rewrite mem_enum.
  rewrite {}[in X in X = _]phiD.
  have : uniq (enum (S_ phi)) by exact: enum_uniq.
  have : forall i, i \in (enum (S_ phi)) -> (i \in S_ phi).
    by move=> ?; rewrite mem_enum.
  rewrite /R /(image _ _); elim: (enum (S_ phi)) => [| a l ihl] l_irr /= U_l.
    rewrite /orthonormal /= !big_nil rmorph0 subr0; split => //.
    apply/eqP; rewrite -cfnorm_eq0.
    by case: tau_iso => ->; rewrite ?cfun0_zchar // cfnorm_eq0 eqxx.
  have S_phia : a \in S_ phi by apply: l_irr; rewrite mem_head.
  case/andP: U_l => nal U_l.
  have {ihl} [| ofl taul] := (ihl _ U_l). 
    by move=> i li; apply: l_irr; rewrite in_cons li orbT.
  have /(h1 _) [_ oa atau] : 'chi_a \in calI.
    by apply: chi_calI; apply/S_calSP; exists phi.
  rewrite orthonormal_cat oa ofl /=; split => [{atau taul}|].
  + apply/orthogonalP=> psi1 psi2 R1psi1; case/mem_flatten_im=> b lb R1psi2.
    have {l_irr} S_phib : b \in S_ phi by apply: l_irr; rewrite mem_behead.
    suff : orthogonal 'chi_a ('chi_b :: (('chi_b)^*)%CF) by exact: (aux phi phi).
    apply/andP; rewrite /=  - conjC_IirrE cfdot_irr.
    have /negPf -> : a != b by move: nal; apply: contra; move/eqP->.
    rewrite eqxx /= andbT; split=> //; apply/eqP; apply/orthoP.
    have irr_a : a \in irr_constt phi by move: S_phia; rewrite inE.
    have irr_bC : conjC_Iirr b \in irr_constt  (phi^*)%CF.
    rewrite inE conjC_IirrE cfdot_conjC; move: S_phib; rewrite inE conjC_eq0.
      by rewrite inE.
    apply: (calS_chi_ortho phi (phi^*)%CF _ (ccS _ _) a (conjC_Iirr b)) => //.
    apply/orthoP; case/pairwise_orthogonalP: calS_portho=> _ -> //; rewrite ?ccS //.
    by move/hasPn: nrS => /(_ _ calS_phi); rewrite eq_sym.
  + rewrite big_cons addrAC rmorphD /= opprD addrA -addrA [- _ + _]addrC.
    by rewrite big_cat /= -atau -taul -linearD.
- move=> phi psi calS_phi calS_psi /andP [] /and3P /= [/eqP opsi_phi /eqP opsi_phiC _] _.
  apply/orthogonalP => Rpsi Rphi; rewrite /R => Rpsi_in Rphi_in.
  case: (mem_flatten_im Rphi_in) => iphi Scphi {Rphi_in} Rphi_in.
  case: (mem_flatten_im Rpsi_in) => ipsi Scpsi {Rpsi_in} Rpsi_in.
  move: Scphi Scpsi; rewrite !mem_enum => Scphi Scpsi.
  suff ochi : orthogonal 'chi_ipsi ('chi_iphi :: (('chi_iphi)^*)%CF).
    exact: (aux psi phi ipsi iphi).
  rewrite orthogonal_sym orthogonal_cons.
  case/pairwise_orthogonalP: oI => _ oI.
  have Scphi' :  iphi \in irr_constt phi by move: Scphi; rewrite inE.
  have Scpsi' :  ipsi \in irr_constt psi by move: Scpsi; rewrite inE.
  have phi_char := (calS_char _ calS_phi); have psi_char := (calS_char _ calS_psi).
  rewrite (irr_constt_ortho phi_char psi_char) //=; last first.
    by rewrite orthogonal_sym; apply/orthoP.
  rewrite orthogonal_sym -conjC_IirrE.
  rewrite (irr_constt_ortho psi_char (cfConjC_char phi_char)) //.
    by apply/orthoP.
  by rewrite inE conjC_IirrE cfdot_conjC fmorph_eq0.
Qed.

End Twelve2.

Section Twelve3.

Lemma PF_12_3 L1 L2 (L1type : FTtype L1 == 1%N) (L2type : FTtype L2 == 1%N)
  (maxL1 : L1 \in 'M)(maxL2 : L2 \in 'M)
  (H1 := L1`_\F%G) (H2 := L2`_\F%G) 
  (calS1 := seqIndD H1 L1 H1 1)(calS2 := seqIndD H2 L2 H2 1) 
  (R1 := sval (FPtype1_calS_subcoherent maxL1 L1type))
  (R2 := sval (FPtype1_calS_subcoherent maxL2 L2type)) : 
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
Local Notation scohS_ := FPtype1_calS_subcoherent.
case: (scohS_ _ _) @R1 => /= R1; set R1' := sval _ => [[subcoh1 hR1' defR1']].
case: (scohS_ _ _) @R2 => /= R2; set R2' := sval _ => [[subcoh2 hR2' defR2']].
move=> L12_non_conj chi1 chi2 calS1_chi1 calS2_chi2. 
apply/orthogonalP=> a b R1a R2b. 
pose tau1 := FT_Dade0 maxL1; pose tau2 := FT_Dade0 maxL2.
suffices{b R2b}: '[a, tau2 (chi2 - chi2^*%CF)] = 0.
  apply: contra_eq => nz_ab; rewrite /tau2.
  have [_ _ _ /(_ chi2)[//|Z_R2 o1R2 ->] _] :=  subcoh2.
  suffices [e ->]: {e | a = if e then - b else b}.
    rewrite -scaler_sign cfdotZl cfdotC -(eq_bigr _ (fun _ _ => scale1r _)).
    by rewrite cfproj_sum_orthonormal // conjC1 mulr1 signr_eq0.
  have [_ _ _ /(_ chi1)[//|Z_R1 /orthonormalP[_ oR1] _] _] := subcoh1.
  have [_ oR2] := orthonormalP o1R2.
  have Z1a: a \in dirr G by rewrite dirrE Z_R1 //= oR1 ?eqxx.
  have Z1b: b \in dirr G by rewrite dirrE Z_R2 //= oR2 ?eqxx.
  move/eqP: nz_ab; rewrite cfdot_dirr //.
  by do 2?[case: eqP => [-> | _]]; [exists true | exists false | ].
Admitted.

(* Hypothesis 12.1 *)
(* Variables (L1 L2 : {group gT}). *)

(* Hypothesis maxL1 : L1 \in 'M. *)
(* Hypothesis maxL2 : L2 \in 'M. *)

(* Hypothesis L1type : FTtype L1 == 1%N. *)
(* Hypothesis L2type : FTtype L2 == 1%N. *)

(* Local Notation "` 'L1'" := (gval L1) (at level 0, only parsing) : group_scope. *)
(* Local Notation "` 'L2'" := (gval L2) (at level 0, only parsing) : group_scope. *)
(* Local Notation H1 := `L1`_\F%G. *)
(* Local Notation H2 := `L2`_\F%G. *)
(* Local Notation "` 'H1'" := `L1`_\F (at level 0) : group_scope. *)
(* Local Notation "` 'H2'" := `L2`_\F (at level 0) : group_scope. *)

(* Local Notation H1' := H1^`(1)%G. *)
(* Local Notation "` 'H1''" := `H1^`(1) (at level 0) : group_scope. *)

(* Local Notation H2' := H2^`(1)%G. *)
(* Local Notation "` 'H2''" := `H2^`(1) (at level 0) : group_scope. *)

(* Hypothesis L12_non_conj : `L2 \notin L1 :^: G. *)

(* Let calS1 := seqIndD H1 L1 H1 1%G. *)
(* Let calS2 := seqIndD H2 L2 H2 1%G. *)

(* Let tau1 := FT_Dade0 maxL1. *)
(* Let tau2 := FT_Dade0 maxL2. *)

(* Let R1 := sval (FPtype1_calS_subcoherent maxL1 L1type). *)
(* Let R2 := sval (FPtype1_calS_subcoherent maxL2 L2type). *)


(* Lemma PF_12_3 : {in calS1 & calS2,  *)
(*   forall chi1 chi2, orthogonal (R1 chi1) (R2 chi2)}. *)
(* Proof. *)
(* Admitted. *)

End Twelve3.

Section Twelve_4_to_6.

Variable L : {group gT}.

Hypotheses (maxL : L \in 'M) .


Local Notation "` 'L'" := (gval L) (at level 0, only parsing) : group_scope.
Local Notation H := `L`_\F%G.
Local Notation "` 'H'" := `L`_\F (at level 0) : group_scope.

Let calS := seqIndD H L H 1%G.
Let tau := FT_Dade0 maxL.


Section Twelve_4_5.

Hypothesis Ltype1 : FTtype L == 1%N.

End Twelve_4_5.

(* This will be (12.6). *)
Lemma FT_seqInd_Frobenius_coherence :
    [Frobenius L with kernel H] ->
  {subset calS <= irr L} /\ coherent calS L^# tau.
Proof. move: maxL. admit. Qed.

End Twelve_4_to_6.

Section Twelve_8_to_16.

Variable p : nat.

(* Equivalent reformultaion of hypothesis 12.8 avoiding quotients *)
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
Admitted.

Variables (L : {group gT}) (x : gT).
Hypotheses (abP0 : abelian P0) (prankP0 : 'r_p(P0) = 2).
Hypotheses (maxL : L \in 'M) (sP0_Ls : P0 \subset L`_\s).
Hypotheses (P0_1s_x : x \in 'Ohm_1(P0)^#) (sNxM : 'N(<[x]>) \subset M).
Hypotheses (not_sCxK' : ~~ ('C_K[x] \subset K')) (not_sCxL : ~~ ('C[x] \subset L)).

Let H := L`_\F%G.

Let frobL : [Frobenius L with kernel H].
Admitted.

Let defM : K ><| (M :&: L) = M.
Admitted.

Let sML_H : M :&: L \subset H.
Admitted.

Let E := sval (sigW (existsP frobL)).
Let e := #|E|.

Let defL: H ><| E = L.
Proof. by rewrite /E; case: (sigW _) => E0 /=/Frobenius_context[]. Qed.

Let PF12_12 : cyclic E /\ (e %| p.-1) || (e %| p.+1).
Admitted.

Import PFsection7.

Let calS := seqIndD H L H 1.
Notation tauL := (FT_Dade0 maxL).
Notation rhoL := (invDade (FT_Dade0_hyp maxL)).

Section Twelve_13_to_16.

Variables (tau1 : {additive 'CF(L) -> 'CF(G)}) (chi : 'CF(L)).
Hypothesis cohS : coherent_with calS L^# tauL tau1.
Hypotheses (Schi : chi \in calS) (chi1 : chi 1%g = e%:R).
Let psi := tau1 chi.

Let PF12_14 : {in K, forall g, psi (x * g)%g = chi x} /\ rhoL psi x = chi x.
Admitted.

Let rhoM := (invDade (FT_Dade1_hyp maxL)).

Let PF12_15 :
  [/\ {in K^#, forall g, rhoM psi g = psi g},
      {in K :\: K' &, forall g1 g2, psi g1 = psi g2}
    & {in K :\: K', forall g, psi g \in Cint}].
Admitted.

Lemma PF12_16_inner : False.
move: cohS Schi. admit. Qed.

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


