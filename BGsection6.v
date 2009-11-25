Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import abelian gfunc pgroups nilpotent gprod commutators.
Require Import BGsection1 coprime_act.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Test.

Variable gT : finGroupType.

Lemma six3a : forall G H K : {group gT},
   solvable G -> Hall G H -> H ><| K = G -> H \subset G^`(1) -> 
   [~: H, K] = H /\ 'C_H(K) \subset H^`(1).
Proof.
move=> G H K solG hallH; case/sdprodP=> _ defG nHK tiHK sHG'.
set Hstar := [~: H, K].
case/andP: (hallH) => sHG.
rewrite -divgS // -defG TI_cardMg // mulKn // => coHK.
pose Gbar := G / Hstar; pose Hbar := H / Hstar; pose Kbar := K / Hstar.
have tiHbKb : Hbar :&: Kbar = 1
  by rewrite -quotientGI // ?tiHK ?quotient1 // commg_subl. 
have GHxK : Gbar = Hbar \x Kbar.
  rewrite dprodE /Gbar -?defG ?tiHbKb //; first by rewrite quotientMl // normsRl.
  by rewrite quotient_cents2 //; [ rewrite normsRl | rewrite normsRr ].
have sHbH'K' : Hbar \subset Hbar^`(1) * Kbar^`(1).
  have p1 : G \subset 'N(Hstar).   
    by apply: (subset_trans _ (commg_norm _ _)); rewrite norm_mulgenEr ?defG.
  have sHbGb' : Hbar \subset Gbar^`(1).
    by rewrite /Hbar derg1 /Gbar -quotientR // quotientS.
  apply: (subset_trans sHbGb').
  rewrite !derg1 -![[~: _, _]]lcn1 /Gbar -defG -lcn_mul ?quotient_cents2r //.
  by rewrite !lcn1 !derg1 -quotientMl ?normsRl.
have {tiHbKb} tiHbKb' : Hbar :&: Kbar^`(1) = 1.
  have s1G : forall G : {group coset_of Hstar}, 1%G \subset G. (* ??? *)
    by move=>*;apply/subsetP=>x; case/set1P=>->; apply: group1.
  apply/eqP; rewrite eqEsubset subsetI !s1G !andbT.  
  have aux : Hbar :&: Kbar^`(1) \subset Hbar :&: Kbar
    by rewrite setIS // der_sub.
  by apply: (subset_trans aux); rewrite tiHbKb.
have nH'K' : Kbar^`(1) \subset 'N(Hbar^`(1)).
  by rewrite normsR // (subset_trans (der_sub _ _)) // quotient_norms.
have {nH'K' tiHbKb' sHbH'K'} Hb'eqHb : Hbar^`(1) = Hbar. 
  rewrite -(@mul1g _ Hbar^`(1)) -tiHbKb' group_modr /= -/Hbar ?der_sub0 //.
  by apply/setIidPl; rewrite -norm_mulgenEl // mulgenC norm_mulgenEr.
have {Hb'eqHb} HbT : Hbar = 1.
  have solHb': solvable Hbar^`(1). 
    by rewrite Hb'eqHb quotient_sol // (solvableS _ solG).
  apply/eqP; apply: (implyP (forallP solHb' _)); rewrite /= -/Hbar.
  by rewrite -{1}Hb'eqHb subsetI subxx.
have {HbT GHxK Gbar Kbar Hbar} fstHalf: [~: H, K ] = H. 
  apply/eqP; rewrite eqEsubset /Hstar !commg_subl nHK /=.
  by rewrite -quotient_sub1 -/Hbar ?HbT ?commg_norml.
pose H' := H^`(1).
suff E: 'C_H(K) / H' = 1. 
  rewrite -quotient_sub1 ?E // (subset_trans _ (commg_norml _ _)) //. 
  by rewrite (subset_trans _ (subsetIl _ 'C(K))) //.
have abelHH' : abelian (H / H') by apply: der_abelian.
have copH' : coprime #|H / H'| #|K / H'| by apply: coprime_morph.
have sKH'NormHH' : K / H' \subset 'N(H / H') by rewrite quotient_norms.
have nH'K : K \subset 'N(H') by apply: char_norm_trans nHK; apply: der_char.
have: H' <| H by apply: der_normal.
case/andP=> sHH' nH'H.
rewrite coprime_quotient_cent //= -/H' //.
  by rewrite -fstHalf quotientR //= -/H' coprime_abel_cent_TI.
exact: solvableS solG.
Qed.

End Test.
