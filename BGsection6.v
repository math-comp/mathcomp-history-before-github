(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import abelian gfunc pgroups nilpotent gprod center commutators.
Require Import BGsection1 coprime_act sylow.
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Six.

Variable gT : finGroupType. 
Implicit Types G H K : {group gT}.

(* 6.3(a), page ... *)
Lemma solvable_hall_dprod_der_subset_comm_centr_compl : forall G H K,
   solvable G -> Hall G H -> H ><| K = G -> H \subset G^`(1) -> 
   [~: H, K] = H /\ 'C_H(K) \subset H^`(1).
Proof.
move=> G H K solG hallH; case/sdprodP=> _ defG nHK tiHK sHG'.
case/andP: hallH => sHG; case/andP: (der_normal H 0) =>  sHH' nH'H.
rewrite -divgS // -defG TI_cardMg // mulKn // => coHK.
have{solG} solH : solvable H by apply: solvableS solG.
set R := [~: H, K]; have sRH: R \subset H by rewrite commg_subl.
have tiHbKb : H / R :&: K / R = 1 by rewrite -quotientGI ?tiHK ?quotient1.
have sHbH'K' : H / R \subset (H / R)^`(1) * (K / R)^`(1).
  have nRG: G \subset 'N(R) by rewrite -defG -norm_mulgenEr ?commg_norm.
  rewrite -(lcn_mul 1) ?quotient_cents2r //= -quotientMl ?normsRl //= -/R.
  by rewrite defG -['L_1(_)]quotientR // quotientS.
have {tiHbKb} tiHbKb' : H / R :&: (K / R)^`(1) = 1.
  by apply/trivgP; rewrite /= -tiHbKb setIS // der_sub.
have nH'K' : (K / R)^`(1) \subset 'N((H / R)^`(1)).
  by rewrite normsR // (subset_trans (der_sub _ _)) // quotient_norms.
have {nH'K' tiHbKb'} HR'HR : (H / R)^`(1) = H / R. 
  rewrite -[_^`(_)]mulg1 -tiHbKb' setIC group_modl ?der_sub0 // setIC.
  by apply/setIidPl.
have {HR'HR} HbT : (H / R) = 1.
  have solHb': solvable (H / R)^`(1) by rewrite HR'HR quotient_sol.
  by rewrite (eqP (implyP (forallP solHb' _) _)) //= -{1}HR'HR subsetI subxx.
have {HbT sHbH'K' sRH} fstHalf: [~: H, K ] = H. 
  apply/eqP; rewrite eqEsubset -/R //= !commg_subl nHK /=.
  by rewrite -quotient_sub1 ?HbT ?commg_norml.
suff {R} E: 'C_H(K) / H^`(1) = 1 by rewrite -quotient_sub1 ?E // subIset // nH'H.
have abelHH' : abelian (H / H^`(1)) by apply: der_abelian.
have copHKH' : coprime #|H / H^`(1)| #|K / H^`(1)| by apply: coprime_morph.
have nKH'HH' : K / H^`(1) \subset 'N(H / H^`(1)) by rewrite quotient_norms.
have nH'K : K \subset 'N(H^`(1)) by apply: char_norm_trans nHK; apply: der_char.
by rewrite coprime_quotient_cent //= -{4}fstHalf quotientR ?coprime_abel_cent_TI.
Qed.

Let six3a := solvable_hall_dprod_der_subset_comm_centr_compl.

(* TODO: 
    - weaken to solvable H 6.3a and remove solvable G in 6.3b 
    - see if #|G : G'| is more convenient for 6.3b
*)

(* 6.3(b) *)
Lemma der_nil_prime_idx_hall_comm_compl: forall G,
   solvable G -> nilpotent G^`(1) -> prime #|G / G^`(1)| -> 
    Hall G G^`(1) /\ 
    (forall K, G^`(1) ><| K = G -> G^`(1) = [~: G, K]).
Proof.
move=> G solG nilG' /=; set G' := G^`(1); set p := #|G / G'| => prime_p.
have nsG'G: G' <| G := der_normal G 0; have [sG'G nG'G] := andP nsG'G.
pose D := G / 'O_p^'(G').
have nsOG'G: 'O_p^'(G') <| G := char_normal_trans (pcore_char _ _) nsG'G.
have nOG'G := normal_norm nsOG'G.
have{nilG'} pgD : p.-group(D).
  rewrite /pgroup card_quotient -?(LaGrange_index sG'G (pcore_sub _ _)) //= -/G'.
  rewrite pnat_mul // -card_quotient // pnat_id //= -pnatNK.
  by case/and3P: (nilpotent_pcore_Hall p^' nilG').
have cyD : cyclic D.
  apply: (cyclic_pgroup_quo_der1_cyclic pgD).
  rewrite -[_^`(1)]quotientR //= (isog_cyclic (third_isog _ _ _)) ?pcore_sub //=.
  exact: prime_cyclic.
have eG'OpG' : G' = 'O_p^'(G').
  apply/eqP; rewrite eqEsubset pcore_sub -quotient_cents2 ?normal_norm //= -/D.
  by rewrite -abelianE cyclic_abelian.
have hallG' : Hall G G'.
  rewrite /Hall sG'G -?card_quotient // eG'OpG' //= -/p.
  by rewrite coprime_sym (pnat_coprime _ (pcore_pgroup _ _)) ?pnat_id.
split=> // K sdG'K; case/six3a: (sdG'K) => //=; rewrite -/G' => defG' _.
case/sdprodP: sdG'K=> _ GHK nKG' tiG'K; rewrite -GHK commMG /= ?defG' //.
rewrite (commG1P _) ?mulg1 //; apply: cyclic_abelian; apply: prime_cyclic.
move: prime_p; rewrite /p card_quotient ?normal_norm // -divgS ?normal_sub //.
by rewrite /= -/G' -GHK TI_cardMg ?mulKn.
Qed.

End Six.
