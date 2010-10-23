(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool eqtype ssrnat seq div fintype finset.
Require Import prime fingroup morphism automorphism quotient gproduct gfunctor.
Require Import cyclic center commutator pgroup nilpotent sylow abelian hall.
Require Import BGsection1 BGappendixAB.

(******************************************************************************)
(*   This file covers most of B & G section 6.                                *)
(* Theorem 6.4 is not proved, since it is not needed for the revised proof of *)
(* the odd order theorem.                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Six.

Variable gT : finGroupType. 
Implicit Types G H K S U : {group gT}.
Implicit Type p : nat.

(* This is B & G, Theorem A.4(b) and 6.1, or Gorenstein 6.5.2, the main Hall- *)
(* Higman style p-stability result used in the proof of the Odd Order Theorem *)
Theorem odd_p_abelian_constrained : forall p (G : {group gT}),
  odd #|G| -> solvable G -> p.-abelian_constrained G.
Proof.
move=> p G; move/odd_p_stable=> stabG; move/solvable_p_constrained=> constrG.
exact: p_stable_abelian_constrained.
Qed.

(* Auxiliary results from AppendixAB, necessary to exploit the results below. *)
Definition center_Puig_char := BGappendixAB.center_Puig_char.
Definition trivg_center_Puig_pgroup := BGappendixAB.trivg_center_Puig_pgroup.

(* The two parts of B & G, Theorem 6.2 are established in BGappendixAB. *)
Theorem Puig_factorisation : forall p G S,
  odd #|G| -> solvable G -> p.-Sylow(G) S -> 'O_p^'(G) * 'N_G('Z('L(S))) = G.
Proof. exact: BGappendixAB.Puig_factorization. Qed.

(* This is the main statement of B & G, Theorem 6.2. It is not used in the    *)
(* actual proof.                                                              *)
Theorem Puig_center_p'core_normal : forall p G S,
  odd #|G| -> solvable G -> p.-Sylow(G) S -> 'O_p^'(G) * 'Z('L(S)) <| G.
Proof.
move=> p G S oddG solG sylS; rewrite -{2}(Puig_factorisation _ _ sylS) //.
have sZL_G := subset_trans (char_sub (center_Puig_char S)) (pHall_sub sylS).
rewrite -!quotientK ?(subset_trans _ (bgFunc_norm _ _)) ?subsetIl //.
by rewrite cosetpre_normal quotient_normal // normalSG.
Qed.

Theorem Puig_center_normal : forall p G S,
  odd #|G| -> solvable G -> p.-Sylow(G) S -> 'O_p^'(G) = 1 -> 'Z('L(S)) <| G.
Proof. exact: BGappendixAB.Puig_center_normal. Qed.

(* This is B & G, Lemma 6.3(a). *)
Lemma solvable_hall_dprod_der_subSset_comm_centr_compl : forall G H K,
    solvable H -> Hall G H -> H ><| K = G -> H \subset G^`(1) -> 
  [~: H, K] = H /\ 'C_H(K) \subset H^`(1).
Proof.
move=> G H K solG hallH; case/sdprodP=> _ defG nHK tiHK sHG'.
case/andP: hallH => sHG; case/andP: (der_normal 1 H) =>  sHH' nH'H.
rewrite -divgS // -defG TI_cardMg // mulKn // => coHK.
set R := [~: H, K]; have sRH: R \subset H by rewrite commg_subl.
have tiHbKb : H / R :&: K / R = 1 by rewrite -quotientGI ?tiHK ?quotient1.
have sHbH'K' : H / R \subset (H / R)^`(1) * (K / R)^`(1).
  have defGq: (H / R) \* (K / R) = G / R.
    by rewrite cprodE 1?centsC ?quotient_cents2r //= -quotientMl ?normsRl ?defG.
  case/cprodP: (der_cprod 1 defGq) => _ -> _ /=.
  by rewrite -quotient_der ?quotientS // -defG -norm_mulgenEr ?commg_norm.
have {tiHbKb} tiHbKb' : H / R :&: (K / R)^`(1) = 1.
  by apply/trivgP; rewrite /= -tiHbKb setIS // der_subS.
have nH'K' : (K / R)^`(1) \subset 'N((H / R)^`(1)).
  by rewrite normsR // (subset_trans (der_subS _ _)) // quotient_norms.
have {nH'K' tiHbKb'} HR'HR : (H / R)^`(1) = H / R. 
  rewrite -[_^`(_)]mulg1 -tiHbKb' setIC group_modl ?der_sub // setIC.
  by apply/setIidPl.
have {HR'HR} HbT : (H / R) = 1.
  have solHb': solvable (H / R)^`(1) by rewrite HR'HR quotient_sol.
  by rewrite (eqP (implyP (forallP solHb' _) _)) //= -{1}HR'HR subsetI subxx.
have {HbT sHbH'K' sRH} fstHalf: [~: H, K ] = H. 
  apply/eqP; rewrite eqEsubset -/R //= !commg_subl nHK /=.
  by rewrite -quotient_sub1 ?HbT ?commg_norml.
suff {R} E: 'C_H(K) / H^`(1) = 1 by rewrite -quotient_sub1 ?E ?subIset // nH'H.
have abelHH' : abelian (H / H^`(1)) by apply: der_abelian.
have copHKH' : coprime #|H / H^`(1)| #|K / H^`(1)| by apply: coprime_morph.
have nKH'HH' : K / H^`(1) \subset 'N(H / H^`(1)) by rewrite quotient_norms.
have nH'K : K \subset 'N(H^`(1)) by apply: char_norm_trans nHK; apply: der_char.
by rewrite coprime_quotient_cent //= -{4}fstHalf quotientR ?coprime_abel_cent_TI.
Qed.

(* This is B & G, Lemma 6.3(b) *)
Lemma der_nil_prime_idx_hall_comm_compl: forall G,
    nilpotent G^`(1) -> prime #|G / G^`(1)| -> 
  Hall G G^`(1) /\ (forall K, G^`(1) ><| K = G -> G^`(1) = [~: G, K]).
Proof.
move=> G nilG' /=; set G' := G^`(1); set p := #|G / G'| => prime_p.
have nsG'G: G' <| G := der_normal 1 G; have [sG'G nG'G] := andP nsG'G.
pose D := G / 'O_p^'(G').
have nsOG'G: 'O_p^'(G') <| G := char_normal_trans (pcore_char _ _) nsG'G.
have nOG'G := normal_norm nsOG'G; have solG' := nilpotent_sol nilG'.
have{nilG'} pgD : p.-group(D).
  rewrite /pgroup card_quotient -?(LaGrange_index sG'G (pcore_sub _ _)) //=.
  rewrite pnat_mul // -card_quotient // pnat_id //= -pnatNK.
  by case/and3P: (nilpotent_pcore_Hall p^' nilG').
have cyD : cyclic D.
  apply: (cyclic_pgroup_quo_der1_cyclic pgD); rewrite -[_^`(1)]quotientR //=.
  by rewrite (isog_cyclic (third_isog _ _ _)) ?pcore_sub //= prime_cyclic.
have eG'OpG' : G' = 'O_p^'(G').
  apply/eqP; rewrite eqEsubset pcore_sub -quotient_cents2 ?normal_norm //= -/D.
  by rewrite -abelianE cyclic_abelian.
have hallG' : Hall G G'.
  rewrite /Hall sG'G -?card_quotient // eG'OpG' //= -/p.
  by rewrite coprime_sym (pnat_coprime _ (pcore_pgroup _ _)) ?pnat_id.
have six3a := solvable_hall_dprod_der_subSset_comm_centr_compl.
split=> // K sdG'K; case/six3a: (sdG'K); rewrite //= -/G' => defG' _ {six3a}.
case/sdprodP: sdG'K=> _ GHK nKG' tiG'K; rewrite -GHK commMG /= ?defG' //.
rewrite (commG1P _) ?mulg1 //; apply: cyclic_abelian; apply: prime_cyclic.
move: prime_p; rewrite /p card_quotient ?normal_norm // -divgS ?normal_sub //.
by rewrite /= -/G' -GHK TI_cardMg ?mulKn.
Qed.

(* This is B & G, Lemma 6.5(a) *)
Lemma prod_norm_coprime_subs_derI : forall G K U H, 
    K * U = G -> K <| G -> H \subset U -> coprime #|H| #|K| ->
  H :&: G^`(1) = H :&: U^`(1).
Proof.
move=> G K U H defG nKG sHU copHK; set pi := \pi(H); simpl in pi.
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
  rewrite comm_mulgenE // -comKU -mulgA mulGid comKU mulSg ?commMG ?normsRr //.
  by rewrite -{4}(@mulGid _ K) mulgSS ?(der_sub 1) ?commg_subr.
have abelGKU : abelian ( G / (K <*> U')) by rewrite sub_der1_abelian.
have sKU'G : K <*> U' \subset G. 
  by rewrite mulgen_subG // sKG (subset_trans _ sUG) // (der_sub 1).
have nKU'G : G \subset 'N(K <*> U').
  by rewrite -commg_subl //= (subset_trans _ keyprop) // commgSS.
have{abelGKU} sG'KU' : G' \subset K * U'.
  by rewrite /G' {1}[_^`(_)]derg1 -norm_mulgenEr // -quotient_cents2.
have nUKU' : (U :&: K) \subset 'N(U') by apply: normsRl; rewrite subIset ?subxx.
have{sG'KU'} sHG'UKU': H :&: G' \subset (U :&: K) * U'.
  by rewrite group_modr ?der_sub // (subset_trans _ (setIS _ sG'KU')) // setSI.
have {keyprop} squot : (U :&: G') / U' \subset (U :&: K) <*> U' / U'.
  rewrite quotientS // norm_mulgenEl // group_modr ?setIS ?der_sub //. 
  by rewrite -norm_mulgenEr ?keyprop. 
have isoquot : (U :&: K) <*> U' / U' \isog (U :&: K) / (U' :&: K).
  have <- : (U' :&: (U :&: K)) = (U' :&: K).
    rewrite setIA (_:U^`(1) :&: U = U^`(1)) //; apply/eqP; rewrite eqEsubset.
    by rewrite subsetIl subsetI der_sub subxx.
  rewrite quotient_mulgenr // isog_sym; apply: second_isog. 
  exact: (subset_trans (subsetIl _ _) (lcn_norm 2 U)). 
have pi'UKU'K : pi^'.-group ((U :&: K) / (U' :&: K)).
  rewrite morphim_pgroup // -[_.-group _]coprime_pi' //.
  by rewrite (@coprimegS _ K) ?subsetIr.
have {squot isoquot} pi'UG'U' : pi^'.-group((U :&: G') / U').
  by apply: (pgroupS squot); rewrite /pgroup (isog_card isoquot).
have piHG'U' : pi.-group ((H :&: G') / U').
  apply: morphim_pgroup=> /=.
  by apply: (@pgroupS _ _ H); rewrite ?subIset ?subxx // /pi /pgroup pnat_pi.
have pi'HG'U' : pi^'.-group ((H :&: G') / U').
  by rewrite (pgroupS _ pi'UG'U') // quotientS // setSI.
have c1 : #|(H :&: G') / U'| = 1%N := (pnat_1 piHG'U' pi'HG'U').
have sHG'U' : H :&: G' \subset U'.
  have ? : (H :&: G') \subset 'N(U').
    by rewrite (subset_trans _ (lcn_norm 2 _)) // subIset // sHU.
  by rewrite -quotient_sub1 //= -(card1_trivg c1).
by apply/eqP; rewrite eqEsubset subsetI sHG'U' subsetIl /= setIS // (lcnS 2).
Qed.

(* This is B & G, Lemma 6.5(c) *)
Lemma sol_prod_norm_coprime_subs_centralise_conjg : forall G K U H g, 
    solvable G -> K * U = G -> K <| G -> H \subset U -> coprime #|H| #|K| ->
    g \in G -> H :^ g \subset U -> 
  exists2 c, c \in 'C_K(H) & exists2 u, u \in U & g = c * u.
Proof.
move=> G K U H g solG defG; case/andP=> sKG sGnK sHU copHK; rewrite -defG.
case/mulsgP=> k u kK uU defg sHgU; pose pi := \pi(H); simpl in pi.
have comKU : commute K U by apply/comm_group_setP; rewrite defG groupP.
have sUG : U \subset G by rewrite -defG mulg_subr.
have comKH : commute H K. 
  by apply: normC; rewrite (subset_trans _ sGnK) // (subset_trans sHU).
have sHkU : H :^ k \subset U.
  rewrite -(@lcoset_id _ U u^-1^-1) ?groupV // -(@rcoset_id _ U u^-1) ?groupV//.
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
  rewrite /pi Hall_pi // /Hall subsetI sHU mulgen_subl ?(coprime_dvdr _ cpHK)//.
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
  rewrite /c conjsgM HkHw defw -conjsgM -mulgA mulgV mulg1.
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

(* This is B & G, Lemma 6.5(b) *)
Lemma sol_prod_norm_coprime_subs_norm_cent_prod : forall G K U H, 
    solvable G -> K * U = G -> K <| G -> H \subset U -> coprime #|H| #|K| ->
  'N_G(H) = 'C_K(H) * 'N_U(H).
Proof.
move=> G K U H solG defG nKG sHU copHK.
apply/eqP; rewrite eqEsubset; apply/andP; split; last first.
  apply/subsetP=>c; case/mulsgP=>k u; case/setIP=> kK kC; case/setIP=> uU uN ->.
  by rewrite -defG in_setI mem_mulg //= groupM // (subsetP (cent_sub _)).
apply/subsetP=> n; case/setIP=> nG; move/normP=> HnH.
have sHnU : H :^ n \subset U by rewrite HnH (subset_trans sHU).
case: (sol_prod_norm_coprime_subs_centralise_conjg _ _ nKG sHU _ nG) =>//.
move=> c cC [u uU defn]; rewrite defn mem_mulg // in_setI uU /=. 
have HcH : H :^ c = H.
  by apply/normP; rewrite (subsetP (cent_sub _)) //; case/setIP: cC. 
by apply/normP; rewrite -{1}HcH -conjsgM -defn. 
Qed.

(* This is B & G, Lemma 6.6(a) *)
Lemma sol_Sylow_plength1_pseries_pcore: forall G S p, 
    solvable G -> p.-Sylow(G) S -> p.-length_1 G ->
  S * 'O_p^'(G) = 'O_{p^',p}(G) /\ 'O_p^'(G) * 'N_G(S) = G.
Proof.
move=> G S p solG psylS pl1G; set M := 'O_p^'(G); set U := 'N_G(S).
have sSG : S \subset G by case/andP: psylS.
have nOp'G : G \subset 'N('O_p^'(G)) := char_norm (pcore_char _ _).
have nSOp'G : S \subset 'N('O_p^'(G)) := subset_trans sSG nOp'G.
rewrite plength1_pcore_quo_Sylow in pl1G.
have nOp'pGG : 'O_{p^',p}(G) <| G by apply: pseries_normal.
have defOp'pG : M * S = 'O_{p^',p}(G).
  rewrite -norm_mulgenEr //; apply: (@quotient_inj _ 'O_p^'(G));rewrite /normal.
  by rewrite mulgen_subl (subset_trans _ nOp'G) // mulgen_subG pcore_sub sSG.
    by rewrite /= -pseries1 pseries_norm2 pseries_sub_catl.
  rewrite /= mulgenC quotient_mulgenr ?(subset_trans _ nOp'G) //=. 
  have {pl1G} pl1G : p.-Sylow(G / 'O_p^'(G)) ('O_{p^',p}(G) / 'O_p^'(G)).
    by rewrite lastI -pseries1 quotient_pseries pseries1 /=.
  rewrite (uniq_normal_Hall pl1G _ _) ?normal_norm ?quotient_normal //=. 
  by apply: Hall_max; exact: morphim_pSylow.
split; first by rewrite normC // defOp'pG.
have sylOP'pS: p.-Sylow('O_{p^',p}(G)) S.
  by rewrite (pHall_subl _ _ psylS) ?pseries_sub//= -defOp'pG mulg_subr ?group1.
rewrite -(Frattini_arg nOp'pGG sylOP'pS) /= -defOp'pG -/U -mulgA.
by rewrite (@mulSGid _ _ S) //= subsetI sSG normG.
Qed.

(* This is B & G, Lemma 6.6(b) *)
Lemma sol_Sylow_plength1_sub_norm_der: forall G S p, 
    solvable G -> p.-Sylow(G) S -> p.-length_1 G -> S \subset G^`(1) -> 
  S \subset ('N_G(S))^`(1).
Proof.
move=> G S p solG psylS;
case/(sol_Sylow_plength1_pseries_pcore solG psylS)=> _ defG sSG' {pl1G solG}.
have [sSG pgS _] := and3P psylS; have nOp'G := char_normal (pcore_char p^' G).
have {sSG} sSNS : S \subset 'N_G(S) by rewrite subsetI sSG normG.
have cop : coprime #|S| #|'O_p^'(G)|.
  by rewrite (pnat_coprime pgS) // [_.-nat_]pcore_pgroup.
rewrite (subset_trans _ (subsetIr S _)) //.
by rewrite -(prod_norm_coprime_subs_derI _ nOp'G _ cop) // subsetI sSG' subxx.
Qed.

(* This is B & G, Lemma 6.6(c) *)
Lemma sol_Sylow_plength1_norm_conj: 
    forall G S (Y : {set gT}) x p, 
    solvable G -> p.-Sylow(G) S -> p.-length_1 G ->
    Y \subset S -> x \in G -> Y :^ x \subset S -> 
  exists2 c, c \in 'C_G(Y) & exists2 g, g \in 'N_G(S) & c * g = x.
Proof.
move=> G S Y x p solG psylS pl1G sYS xG YxS. case/and3P: (psylS)=> sSG pgS _.
have cop : coprime #|<<Y>>| #|'O_p^'(G)|.
  by rewrite (pnat_coprime (pgroupS _ pgS) (pcore_pgroup _ _)) ?gen_subG.
have [_ defG] := (sol_Sylow_plength1_pseries_pcore solG psylS pl1G). 
have nOp'G : 'O_p^'(G) <| G := char_normal (pcore_char _ _).
have sYNS : <<Y>> \subset 'N_G(S).
  by rewrite gen_subG subsetI (subset_trans sYS) // (subset_trans _ (normG _)).
have sYxNS :  <<Y>> :^ x \subset 'N_G(S).
  by rewrite -genJ gen_subG (subset_trans YxS) // subsetI sSG normG.
case/(sol_prod_norm_coprime_subs_centralise_conjg _ defG _ sYNS): sYxNS => // a.
case/setIP => a0 aCY [b bNS ->]; exists a; last exists b=>//; rewrite in_setI.
by rewrite (subsetP (pcore_sub p^' G)) //= -cent_gen.
Qed.

(* This is B & G, Lemma 6.6(d) *)
Lemma sol_Sylow_plength1_cent_conj: forall G S (Q : {group gT}) p, 
    solvable G -> p.-Sylow(G) S -> p.-length_1 G -> p.-subgroup(G) Q -> 
  exists2 x, x \in 'C_G(Q :&: S) & Q :^ x \subset S. 
Proof.
move=> G S Q p solG psS pl1G.
case: (sol_Sylow_plength1_pseries_pcore solG psS pl1G) => defOp'pG defG psgQ.
rewrite plength1_pcore_quo_Sylow in pl1G; have {psgQ} [sQG pgQ] := andP psgQ.
pose M := 'O_p^'(G); have: M <| G := pcore_normal _ _; case/andP=> sMG nMG.
have sMOp'p : M \subset 'O_{p^',p}(G) by rewrite /M -pseries1 pseries_sub_catl.
have [sSG pgS _] := and3P psS; have nMS := subset_trans sSG nMG.
have{defG} defG: 'N_G(S) * M = G by rewrite normC // subIset // nMG.
have{defG sQG} sQMS : Q \subset M <*> S.
  rewrite mulgenC norm_mulgenEl // defOp'pG.
  case: (Sylow_subJ psS sQG pgQ) => x xG sQSx; rewrite (subset_trans sQSx) //.
  rewrite -defG in xG; case/imset2P: xG=> s o sS oO ->; case/setIP: sS=> _ snS.
  rewrite conjsgM (normP snS) -defOp'pG -(mulGid 'O_p^'(G)) mulgA normC /=.
    by rewrite conjsgE !mulgSS ?sub1set ?groupV.
  by rewrite mul_subG ?normG //; case/andP: psS.
have{psS defOp'pG} psSMS : p.-Sylow(M <*> S) S.
  rewrite mulgenC norm_mulgenEl // defOp'pG.
  by rewrite (pHall_subl _ _ psS) ?pseries_sub ///= -defOp'pG mulg_subl ?group1.
case: (Sylow_Jsub psSMS sQMS pgQ)=> w /=; rewrite norm_mulgenEr //= -/M.
case/imset2P=> x y xM yS -> sQxyS {w psSMS sQMS pgQ sMOp'p sSG nMG psGQ pl1G}.
have{y yS sQxyS} sQxS : Q :^ x \subset S.
  have y'S : y^-1 \in 'N(S) by rewrite (subsetP (normG S)) // ?groupV.
  by rewrite -(normP y'S) -sub_conjgV invgK -conjsgM.
exists x; rewrite // inE (subsetP sMG) //=; apply/centP=> z; case/setIP=> Qz Sz.
apply/commgP; rewrite -cycle_eq1 -subG1 cycle_subG /=.
have <-: S :&: M = 1 := coprime_TIg (pnat_coprime pgS (pcore_pgroup _ _)).
rewrite inE -groupV invg_comm groupMl ?groupV // (subsetP sQxS) ?memJ_conjg //.
by rewrite groupMl ?memJ_norm ?groupV // (subsetP nMS).
Qed.

End Six.

(* This is B & G, Theorem 6.7 *)
Theorem sol_plength1_odd_pamxElem_pcore : 
    forall (gT : finGroupType) (G E L: {group gT}) (p : nat), 
    solvable G -> p.-length_1 G -> odd p -> prime p -> 
    E \in 'E*_p(G) -> p^'.-subgroup(G) L -> E \subset 'N(L) ->
  L \subset 'O_p^'(G). 
Proof.
move=> gT G E L p solG pl1G oddp pp Emax; case/andP=> sLG p'L nEL.
wlog K1: gT G E L solG pl1G Emax sLG p'L nEL / 'O_p^'(G) = 1.
  set K := 'O_p^'(G); move/(_ _ (G / K) (E / K) (L / K))%G.
  rewrite morphim_sol // plength1_quo // quotient_pgroup // morphimS //.
  rewrite morphim_norms // trivg_pcore_quotient // quotient_sub1; last first.
    by rewrite (subset_trans sLG) ?bgFunc_norm.
  apply=> //.
  case/pmaxElemP: (Emax); case/pElemP=> sEG pabE maxEG.
  case/(abelemP pp): (pabE) => aE pexp1; have pgE := abelem_pgroup pabE.
  have ? : E \subset 'N(K) := subset_trans sEG (normal_norm (pcore_normal _ _)).
  have pabEK : p.-abelem (E / K). 
    apply/abelemP=> //; rewrite quotient_abelian //; split=> // Kx.
    by case/morphimP=> x Nx Ex ->; rewrite -morphX // pexp1 // morph1.
  have nKG : K <| G by rewrite pcore_normal.
  apply/pmaxElemP; split; first by apply/pElemP; split; rewrite ?quotientS.
  move=> DK; case/pElemP=> sDKGK'; case: (inv_quotientS nKG sDKGK') (sDKGK').
  rewrite /= -/K; move=> D -> sKD sDG sDKGK pabDK sEKDK {sDKGK' DK}.
  have sED : E \subset D by rewrite quotientSGK // in sEKDK.
  case:(Sylow_superset sED pgE) => S psylS sES.
  have [sSD pgS _] := and3P psylS.
  have sSG : S \subset G := subset_trans sSD sDG. 
  have maxES : E \in 'E*_p(S).
    apply/pmaxElemP; split; first by apply/pElemP; split.
    move=> H; case/pElemP=> sHS abH sEH; rewrite maxEG //.
    by apply/pElemP; split; rewrite ?abH ?(subset_trans sHS _).
  have l66a : 'Ohm_1('C_S(E)) = E by exact: Ohm1_cent_max pgS.
  have nKS: S \subset 'N(K) := (subset_trans sSG (char_norm (pcore_char _ _))).
  have TISK: S :&: K = 1.
    by rewrite coprime_TIg ?(pnat_coprime _ (pcore_pgroup _ _)).
  have l66b : (E / K)%G \in 'E*_p(S / K).
    have pgSK : p.-group (S / K) by rewrite quotient_pgroup.
    case/isomP: (quotient_isom nKS TISK) => /=; set f := restrm _ _ => injf <-.
    rewrite -(group_inj (setIidPr sES)) /quotient /=.
    by rewrite -[(_ / _)%G](group_inj (morphim_restrm nKS _ _)) injm_pmaxElem.
  have defSK: S / K = D / K.
    apply/eqP; rewrite eqEcard quotientS //.
    rewrite (card_Hall (morphim_pHall _ nKS psylS)).
    by rewrite /= (part_pnat_id (abelem_pgroup pabDK)).
  rewrite -defSK; rewrite inE in l66b; case/maxgroupP: l66b => _ -> //.
    by apply/pElemP; split; rewrite ?subxx /= ?defSK.
  by rewrite quotientS.
case/pmaxElemP: (Emax); case/pElemP=> sEG pabE maxEG.
case/(abelemP pp): (pabE) => aE pexp1; have pgE := abelem_pgroup pabE.
case:(Sylow_superset sEG pgE) => S psS; case/and3P: (psS) => sSG pgS idxS sES.
have defS : 'O_{p^',p}(G) = S.
  case: (sol_Sylow_plength1_pseries_pcore _ psS pl1G)=>// <- _;
  by rewrite K1 mulg1.
have psOp'pS : p.-Sylow('O_{p^',p}(G)) S.
  by apply: (pHall_subl _ (pseries_sub _ _) psS); rewrite -defS.
have cLS : L \subset 'C_G(S).
  have nSG : G \subset 'N(S). 
    by rewrite -defS /= (pseries_pop2 p K1) char_norm // pcore_char.
  have nLG : L \subset 'N(S) := subset_trans sLG nSG.
  have cLE : L \subset 'C(E).
    apply/commG1P; apply/eqP; rewrite eqEsubset sub1set in_group.
    rewrite -(coprime_TIg (pnat_coprime pgS p'L)) andbC.
    by rewrite setIC commg_subI // subsetI ?subxx ?sES.
  have ? : coprime #|S| #|L| by exact: (pnat_coprime pgS p'L). 
  have ? : odd #|S|.
    rewrite odd_2'nat; apply/pgroupP=> q pq qd.
    move/pgroupP: pgS=> H; have := (H _ pq qd).
    rewrite in_simpl /=; move/eqP=> ->; move: oddp; rewrite odd_2'nat.
    case/andP=> _; move/allP; rewrite primes_prime //= => H1; apply: H1. 
    by rewrite -topredE; apply/orP; left.
  have EEpS : E \in 'E_p(S) by rewrite in_set sES pabE.
  rewrite subsetI sLG /=; apply:(coprime_odd_faithful_cent_abelem EEpS)=>//.
  have maxES : E \in 'E*_p(S).
    apply/pmaxElemP; split; first by apply/pElemP; split.
    move=> H; case/pElemP=> PH1 PH2 sEH; rewrite maxEG //. 
    by apply/pElemP; split; rewrite // (subset_trans _ sSG).
  rewrite (subset_trans cLE) // -{1}(Ohm1_cent_max maxES) // Ohm1Eprime cent_gen.
  rewrite centS // !setIdE setIS //.
  by apply/subsetP=> e; rewrite !inE; move/eqP->.
have sLS : L \subset S.   
  rewrite (subset_trans cLS) //.
  by rewrite (subset_trans (solvable_p_constrained solG psOp'pS)) ?defS ?subxx.
have pgL : p.-group(L) by apply: (pgroupS sLS pgS).
by rewrite -(setIid L) (coprime_TIg (pnat_coprime pgL p'L)) sub1G.
Qed.


