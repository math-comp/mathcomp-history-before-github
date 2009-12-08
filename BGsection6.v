(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import abelian gfunc pgroups nilpotent gprod center commutators.
Require Import BGsection1 coprime_act sylow.
(*******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Six.

Variable gT : finGroupType. 
Implicit Types G H K U: {group gT}.

(* 6.3(a), page 49 *)
Lemma solvable_hall_dprod_der_subset_comm_centr_compl : forall G H K,
   solvable H -> Hall G H -> H ><| K = G -> H \subset G^`(1) -> 
   [~: H, K] = H /\ 'C_H(K) \subset H^`(1).
Proof.
move=> G H K solG hallH; case/sdprodP=> _ defG nHK tiHK sHG'.
case/andP: hallH => sHG; case/andP: (der_normal H 0) =>  sHH' nH'H.
rewrite -divgS // -defG TI_cardMg // mulKn // => coHK.
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

(* TODO: 
    - see if #|G : G'| is more convenient for 6.3b
*)

(* 6.3(b) *)
Lemma der_nil_prime_idx_hall_comm_compl: forall G,
   nilpotent G^`(1) -> prime #|G / G^`(1)| -> 
    Hall G G^`(1) /\ 
    (forall K, G^`(1) ><| K = G -> G^`(1) = [~: G, K]).
Proof.
move=> G nilG' /=; set G' := G^`(1); set p := #|G / G'| => prime_p.
have nsG'G: G' <| G := der_normal G 0; have [sG'G nG'G] := andP nsG'G.
pose D := G / 'O_p^'(G').
have nsOG'G: 'O_p^'(G') <| G := char_normal_trans (pcore_char _ _) nsG'G.
have nOG'G := normal_norm nsOG'G; have solG' := nilpotent_sol nilG'.
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
have six3a := solvable_hall_dprod_der_subset_comm_centr_compl.
split=> // K sdG'K; case/six3a: (sdG'K); rewrite //= -/G' => defG' _ {six3a}.
case/sdprodP: sdG'K=> _ GHK nKG' tiG'K; rewrite -GHK commMG /= ?defG' //.
rewrite (commG1P _) ?mulg1 //; apply: cyclic_abelian; apply: prime_cyclic.
move: prime_p; rewrite /p card_quotient ?normal_norm // -divgS ?normal_sub //.
by rewrite /= -/G' -GHK TI_cardMg ?mulKn.
Qed.

(* 6.5(a) *)
Lemma prod_norm_coprime_subs_derI : forall G K U H, 
  K * U = G -> K <| G -> H \subset U -> coprime #|H| #|K| ->
   H :&: G^`(1) = H :&: U^`(1).
Proof.
move=> G K U H defG nKG sHU copHK; set pi := \pi(#|H|).
have comKU : commute K U by apply/comm_group_setP; rewrite defG groupP.
set G' :=  G^`(1); set U' := U^`(1); case/andP: nKG=> sKG sGnK.
have sUG : U \subset G by rewrite -defG mulg_subr.
have sUnK : U \subset 'N(K) by apply: (subset_trans sUG sGnK).
have nKU' : U' \subset 'N(K) by rewrite comm_subG.
have keyprop : G' \subset K <*> U'.
  rewrite norm_mulgenEr //= /G' /U' !dergSn !derg0 -defG -{2}comm_mulgenE //.
  rewrite commMG ?normsRr ?mulgen_subr //= ?comm_mulgenE //.
  rewrite commGC comKU commMG ?normsRr // [[~:_, _ * _]]commGC -comKU.
  rewrite commMG ?normsRr // -commMG ?normsRr // mulgA.
  rewrite [[~:K,_]]commGC -comm_mulgenE // -commMG ?normsRl ?mulgen_subl //=.
  rewrite comm_mulgenE // -comKU -mulgA mulGid comKU mulSg // commMG ?normsRr //.
  by rewrite -{4}(@mulGid _ K) mulgSS ?(der_sub0 _ 1) ?commg_subr.
have abelGKU : abelian ( G / (K <*> U')) by rewrite sub_der1_abelian.
have sKU'G : K <*> U' \subset G. 
  by rewrite mulgen_subG // sKG (subset_trans _ sUG) // (der_sub0 _ 1).
have nKU'G : G \subset 'N(K <*> U').
  by rewrite -commg_subl //= (subset_trans _ keyprop) // commgSS.
have{abelGKU} sG'KU' : G' \subset K * U'.
  by rewrite /G' {1}[_^`(_)]derg1 -norm_mulgenEr // -quotient_cents2.
have nUKU' : (U :&: K) \subset 'N(U') by apply: normsRl; rewrite subIset ?subxx.
have{sG'KU'} sHG'UKU': H :&: G' \subset (U :&: K) * U'.
  by rewrite group_modr ?der_sub0 // (subset_trans _ (setIS _ sG'KU')) // setSI.
have {keyprop} squot: (U :&: G') / U' \subset (U :&: K) <*> U' / U'.
  rewrite quotientS // norm_mulgenEl // group_modr ?setIS ?der_sub0 //. 
  by rewrite -norm_mulgenEr ?keyprop. 
have isoquot: (U :&: K) <*> U' / U' \isog (U :&: K) / (U' :&: K).
  have <- : (U' :&: (U :&: K)) = (U' :&: K).
    rewrite setIA (_:U^`(1) :&: U = U^`(1)) //; apply/eqP; rewrite eqEsubset.
    by rewrite subsetIl subsetI der_sub0 subxx.
  rewrite quotient_mulgen // isog_sym; apply: second_isog. 
  exact: (subset_trans (subsetIl _ _) (lcn_norm0 U 1)). 
have pi'UKU'K : pi^'.-group ((U :&: K) / (U' :&: K)).
  rewrite morphim_pgroup // -[_.-group _]coprime_pi' //.
  by rewrite (@coprimegS _ K) ?subsetIr.
have {squot isoquot} pi'UG'U'  : pi^'.-group((U :&: G') / U').
  by apply: (pgroupS squot); rewrite /pgroup (isog_card isoquot).
have piHG'U' : pi.-group ((H :&: G') / U').
  apply: morphim_pgroup=> /=.
  by apply: (@pgroupS _ _ H); rewrite ?subIset ?subxx // /pi /pgroup pnat_pi.
have pi'HG'U' : pi^'.-group ((H :&: G') / U').
  by rewrite (pgroupS _ pi'UG'U') // quotientS // setSI.
have c1 : #|(H :&: G') / U'| = 1%N := (pnat_1 piHG'U' pi'HG'U').
have sHG'U' : H :&: G' \subset U'.
  have ? : (H :&: G') \subset 'N(U').
    by rewrite (subset_trans _ (lcn_norm0 _ 1)) // subIset // sHU.
  by rewrite -quotient_sub1 //= -(card1_trivg c1).
by apply/eqP; rewrite eqEsubset subsetI sHG'U' subsetIl /= setIS // (lcnS 1).
Qed.

(* 6.5(c) *)
Lemma sol_prod_norm_coprime_subs_centralise_conjg : forall G K U H, 
  solvable G -> K * U = G -> K <| G -> H \subset U -> coprime #|H| #|K| ->
   forall g, g \in G -> H :^ g \subset U -> 
     exists2 c, c \in 'C_K(H) & exists2 u, u \in U & g = c * u.
Proof.
move=> G K U H solG defG; case/andP=> sKG sGnK sHU copHK g; rewrite -defG.
case/mulsgP=> k u kK uU defg sHgU; pose pi := \pi(#|H|).
have comKU : commute K U by apply/comm_group_setP; rewrite defG groupP.
have sUG : U \subset G by rewrite -defG mulg_subr.
have comKH : commute H K. 
  by apply: normC; rewrite (subset_trans _ sGnK) // (subset_trans sHU).
have sHkU : H :^ k \subset U.
  rewrite -(@lcoset_id _ U u^-1^-1) ?groupV // -(@rcoset_id _ U u^-1) ?groupV //.
  by rewrite -conjsgE; move: sHgU; rewrite defg conjsgM sub_conjg.
have sHkHK : H :^ k \subset H <*> K.
  rewrite comm_mulgenE // -(@mulGid _ K) mulgA comKH -mulgA.
  by rewrite conjsgE !mulgSS ?sub1set ?groupV. 
have sHkHKU : H :^ k \subset H <*> K :&: U by rewrite subsetI sHkHK sHkU.
have sHnK : H \subset 'N(K).
  by rewrite (subset_trans _ sGnK) // (subset_trans sHU) // -defG mulg_subr.
have sHHK : H \subset H <*> K by exact: mulgen_subl.
have cpHK : coprime #|H| #|H <*> K : H|. 
  by rewrite -?divgS //= comm_mulgenE // (coprime_cardMg copHK) 1?mulnC ?mulnK.
have{sHHK} phallH : pi.-Hall ((H <*> K) :&: U) H.
  rewrite /pi Hall_pi // /Hall subsetI sHU mulgen_subl ?(coprime_dvdr _ cpHK) //.
  by apply: indexSg=> /=; rewrite ?subIset ?subxx // subsetI sHU sHHK.
have phallHk : pi.-Hall ((H <*> K) :&: U) (H :^ k).
  rewrite /pi -(@cardJg _ _ k) Hall_pi // /Hall //=. 
  rewrite (subset_trans sHkHKU) ?subxx //= cardJg -?divgS //=. 
  rewrite cardJg divgS /= ?subsetI ?mulgen_subl // (coprime_dvdr _ cpHK) //.
  by rewrite indexSg ?subIset ?subxx // subsetI sHU /= mulgen_subl.
have solHKU : solvable ((H <*> K) :&: U).
  by apply: (solvableS _ solG); rewrite subIset // sUG orbC.
case:(coprime_Hall_trans (sub1G _) _ solHKU phallHk (sub1G _) phallH (sub1G _)).
  rewrite /= (_:#|1%G| = 1%N); last by apply/eqP; rewrite -trivg_card1.
  by rewrite /coprime gcdn1.
move=> w wT /= HkHw {solHKU phallH phallHk pi}. 
have wHKU : w \in H * (K :&: U).
  by rewrite (subsetP _ _ wT) //= subIset ?comm_mulgenE // group_modl // subxx.
case/mulsgP: wHKU => h1 w1 h1H; case/setIP => w1K w1U defw.
pose c := k * w1^-1; pose v := w1 * u.
have cK : c \in K by rewrite groupM ?groupV.
have HcH : H :^ c = H.
  rewrite /c conjsgM (congr_group HkHw) defw -conjsgM -mulgA mulgV mulg1.
  by apply/normP; rewrite (subsetP (normsG _) _ h1H).
exists c; last by exists v; rewrite ?defg /c /v ?groupM //; gsimpl.
rewrite in_setI cK //=; apply/centP=> h hH; apply/eqP.
have KhcKh : K :* h^c = K :* h.
  rewrite conjgE rcosetM rcoset_id ?groupV // rcosetM.
  by rewrite norm_rlcoset -?mulgA ?rcoset_id ?(subsetP sHnK).
have KhchK :  K :* (h^c * h^-1) = K.
  by rewrite rcosetM KhcKh -rcosetM mulgV mulg1.
have hchK : h^c * h^-1 \in K by rewrite -sub1set -KhchK -mulGS subxx. 
have{HcH} hch1 :  c^-1 * h * c * h^-1 = 1.
  apply/set1P; rewrite -(@mulgA _ _ h) -conjgE -set1gE -(coprime_TIg copHK).
  by rewrite in_setI hchK groupM ?groupV // -HcH memJ_conjg.
by rewrite -(inj_eq (mulgI c^-1)) -(inj_eq (mulIg h^-1)); gsimpl; apply/eqP.
Qed.

(* 6.5(b) *)
Lemma sol_prod_norm_coprime_subs_norm_cent_prod : forall G K U H, 
  solvable G -> K * U = G -> K <| G -> H \subset U -> coprime #|H| #|K| ->
  'N_G(H) = 'C_K(H) * 'N_U(H).
Proof.
move=> G K U H solG defG nKG sHU copHK.
apply/eqP; rewrite eqEsubset; apply/andP; split; last first.
  apply/subsetP=> c; case/mulsgP=>k u; case/setIP=> kK kC; case/setIP=> uU uN ->.
  by rewrite -defG in_setI mem_mulg //= groupM // (subsetP (cent_sub _)).
apply/subsetP=> n; case/setIP=> nG; move/normP=> HnH.
have sHnU : H :^ n \subset U by rewrite HnH (subset_trans sHU).
case: (sol_prod_norm_coprime_subs_centralise_conjg _ _ nKG sHU _ nG) =>//.
move=> c cC [u uU defn]; rewrite defn mem_mulg // in_setI uU /=. 
have HcH : H :^ c = H.
  by apply/normP; rewrite (subsetP (cent_sub _)) //; case/setIP: cC. 
by apply/normP; rewrite -{1}HcH -conjsgM -defn. 
Qed.

End Six.

