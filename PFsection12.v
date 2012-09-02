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

Let calI := [seq 'chi_i | i in Iirr_kerD L H 1%G].

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


Lemma FPtype1_Iirr_kerD_subcoherent : 
 {R : 'CF(L) -> seq _ |  subcoherent calI tau R}.
Proof.
apply: irr_subcoherent; last exact: tau_isometry.
split. 
- by apply/dinjectiveP; apply: in2W irr_inj.
- move=> _ /imageP[i _ ->]; exact: mem_irr.
- move=> psi /imageP[i /S_calSP[phi calSphi]]; rewrite inE => irri -> {psi}.
  apply/imageP; exists (conjC_Iirr i); last by rewrite conjC_IirrE.
  apply/S_calSP; exists (phi^*)%CF; first by rewrite ?cfAut_seqInd.
  by rewrite inE irr_consttE conjC_IirrE cfdot_conjC conjC_eq0 -irr_consttE.
- apply/hasPn=> psi; case/imageP => i /S_calSP[phi calSphi].
  rewrite inE => irri -> {psi}; rewrite /cfReal odd_eq_conj_irr1 ?mFT_odd //.
  rewrite  irr_eq1; case/seqIndC1P: (calSphi)=> k kn0 phiE. 
  apply: contra kn0 => /eqP j0;  move: irri; rewrite j0 phiE.
  by rewrite constt_Ind_constt_Res irr0 cfRes_cfun1 -irr0 constt_irr inE.
Qed.

(* This is Peterfalvi (12.2)(b) *)
Lemma FPtype1_calS_subcoherent :
  {R : 'CF(L) -> seq _ | let R1 := sval FPtype1_Iirr_kerD_subcoherent in
    [/\ subcoherent calS tau R,
      forall i (phi := 'chi_i),
      i \in Iirr_kerD L H 1%G -> 
      [/\ (orthonormal (R1 phi)),
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
case: FPtype1_Iirr_kerD_subcoherent => /= R1 [[chi_char nrI ccI] tau_iso oI h1 hortho].
pose R chi := flatten [seq R1 'chi_i | i in S_ chi].
exists R; split => //; last first.
  move=> i Ii.
  have mem_i : 'chi_i \in calI by apply/imageP; exists i.
  move/h1 : (mem_i) => [Zirr oR1 tau_im]; split=> // {h1}.
  move/(f_equal (fun x : 'CF([set: gT]%G)=>  ('[ x ]))): tau_im.
  rewrite cfnorm_orthonormal //.
  have hsubchi : 
    'chi_i - (('chi_i)^*)%CF \in 'Z[calI, L^#].
    have hchi : 'chi_i \in 'Z[calI, L] by rewrite mem_zchar_on // cfun_onG.
    rewrite sub_aut_zchar ?cfAut_zchar // => ? /imageP[j _ ->]; exact: irr_vchar.
  case: tau_iso => h1 _; rewrite {}h1 // {hsubchi}.
  rewrite cfnormBd => [/eqP|]; last first.
    case/pairwise_orthogonalP: oI => _ -> //; rewrite ?ccI //.
    by move/hasPn: nrI => /(_ _ mem_i); rewrite eq_sym.
  by rewrite cfnorm_conjC cfnorm_irr -[1]/(1%:R) -natrD eqC_nat; move/eqP<-.
split.
- by split => // ?; apply: seqInd_char.
- apply: (sub_iso_to _ _ (Dade_Zisometry _)) => // phi.
  have /subsetD1P[_ /setU1K <-] := FTsupp0_sub L.
  rewrite zcharD1E FTsupp0_type1 // => /andP[S_phi phi1nz].
  rewrite zcharD1 {}phi1nz andbT setUC.
  apply: zchar_trans_on phi S_phi => psi calS_psi.
  rewrite zchar_split (seqInd_vcharW calS_psi) /=.
  have [{3}-> _ hCF] := PF_12_2a calS_psi.
  by rewrite rpred_sum.
- exact: seqInd_orthogonal.
- move=> phi calS_phi; case/PF_12_2a: (calS_phi)=> -> _ _.
- admit.
- move=> phi psi calS_phi calS_psi /= /orthogonalP ophi_psiC.
  apply/orthogonalP => Rpsi Rphi; rewrite /R => Rpsi_in Rphi_in.
  (* this could be a more general lemma on seqs *)
  have memR (F : finType)(T : eqType)(f : F -> seq T) (P : pred F) (x : T) :
    x \in flatten [seq f x | x in P] -> exists2 i, i \in P & x \in f i.
  - have: all P (enum P) by apply/allP=> x1; rewrite mem_enum.
    rewrite /(image _ _); elim: (enum P) => //= a l ih /andP[Pa hall]. 
    by rewrite mem_cat; case/orP=> hx; [exists a | apply: ih].
  case: (memR _ _ _ _ _ Rphi_in) => iphi Scphi {Rphi_in} Rphi_in.
  case: (memR _ _ _ _ _ Rpsi_in) => ipsi Scpsi {Rpsi_in} Rpsi_in {memR}.
  have calS_iphi : 'chi_iphi \in calI.
    by rewrite /calI; apply: map_f; rewrite mem_enum; apply/S_calSP; exists phi.
  have calS_ipsi : 'chi_ipsi \in calI.
    by rewrite /calI; apply: map_f; rewrite mem_enum; apply/S_calSP; exists psi.
  suff ochi : orthogonal 'chi_ipsi ('chi_iphi :: (('chi_iphi)^*)%CF).
    by have /orthogonalP -> := (hortho _ _ calS_iphi calS_ipsi ochi).
  rewrite orthogonal_sym orthogonal_cons.
  case/pairwise_orthogonalP: oI => _ oI; apply/andP.
  have aux phi1 phi2 : phi1 \is a character -> phi2 \is a character ->
      phi1 = 'chi_ipsi + phi2 -> '[psi, phi1] != 0.
    move=> char1 char2 ->.    
    have /(constt_charP ipsi) psiP : 
      psi \is a character by move: calS_psi; exact: seqInd_char.
    move: Scpsi; rewrite inE; case/psiP => psi' char_psi' -> {psiP}.
    rewrite cfdotDl cfdotDr cfnorm_irr.
    have /truncCK <- : '['chi_ipsi, phi2] \in Cnat.
      by rewrite cfdotC Cnat_aut Cnat_cfdot_char_irr.
    have /truncCK <- : '[psi', 'chi_ipsi + phi2] \in Cnat.
      by rewrite Cnat_cfdot_char // rpredD ?irr_char.
    by rewrite -[1]/(1%:R) -!natrD; move/charf0P: Cchar->.
  have phi_char : phi \is a character by move: calS_phi; exact: seqInd_char.
  move/(constt_charP iphi): (phi_char) => phiP.
  move: Scphi; rewrite inE; case/phiP => phi' char_phi' phiD {phiP}.
  split; apply/orthoP; rewrite oI ?ccI //.
  + have : '[psi, phi] == 0.
      by apply/eqP; apply: ophi_psiC => //; rewrite ?mem_seq1 ?in_cons eqxx.
    by apply: contraL => /eqP abs; apply: (aux _ phi') => //; rewrite -abs.
  + have : '[psi, phi^*] == 0.
      by apply/eqP; apply: ophi_psiC; rewrite ?mem_seq1 ?in_cons eqxx // orbT.
    apply: contraL => /eqP abs. 
    by apply: (aux _ (phi'^*)%CF); rewrite ?cfConjC_char // phiD rmorphD /= abs.
Qed.

End Twelve2.

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

(* This will be (12.7). *)
Theorem FTtype1_Frobenius M :
  M \in 'M -> FTtype M == 1%N -> [Frobenius M with kernel M`_\F].
Admitted. (* A cinch! *)

(* This will be (12.17). *)
Theorem not_all_FTtype1 : ~~ all_FTtype1 gT.
Admitted.

End PFTwelve.


