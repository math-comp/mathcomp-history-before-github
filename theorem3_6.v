Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms automorphism normal commutators.
Require Import cyclic center pgroups sylow dirprod schurzass hall. 
Require Import coprime_act nilpotent coprime_comm maximal.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.
Section defs.
Variable T : finGroupType.
(* waiting for the actual definition *)
Parameter fitting: {set T} -> {set T}.
Axiom fitting_group_set : forall G : {group T}, group_set (fitting G).
Canonical Structure fitting_group G := Group (fitting_group_set G).

Definition Zgroup (A : {set T}) := 
  forallb V : {group T}, is_sylow A V ==> cyclic V.

End defs.

Notation "''F' ( G )" := (fitting G)
  (at level 8, format "''F' ( G )") : group_scope.
Notation "''F' ( G )" := (fitting_group G) : subgroup_scope.

Lemma cyclicS : forall gT (G H : group gT),
  H \subset G -> cyclic G -> cyclic H. 
Proof.
move=> gT G H HsubG; case/cyclicP=> x gex.
apply/cyclicP. exists (x ^+ (#[x] %/ #|H|)).
have Hdiv: #|H| %| #[x] by rewrite /order -gex; apply: group_dvdn.
move: (cycle_sub_group Hdiv); move/setP=> csg.
move: (csg H); rewrite !inE {csg} => csgH. 
suffices eqG: val H = val <[x ^+ (#[x] %/ #|H|)]>%G by done.
by congr (val _); apply/eqP; rewrite -csgH -gex HsubG eq_refl. 
Qed.

Lemma cyclicJ:  forall gT (G: group gT), forall x:gT,
  cyclic G = cyclic (G :^ x).
have impl: forall gT (G: group gT) x, cyclic G -> cyclic (G :^ x).
  move=> gT G x; case/cyclicP => y ->.
  by rewrite -genJ conjg_set1; apply/cyclicP; exists (y ^ x). 
move=> gT G x; apply/idP/idP; first by apply: impl.
rewrite -{2}(conjsgK x G). apply: impl.
Qed.

Lemma cyclic_morphim : forall (gT rT : finGroupType) (G D : group gT)
                              (f : {morphism D >-> rT}),
  cyclic G -> cyclic (f @* G).
Proof.
move=> gT rt G D f; move/(cyclicS (subsetIr D _)).
case/cyclicP=> x /= GDx.
have Dx: x \in D by have:= cyclenn x; rewrite -GDx inE; case/andP.
rewrite -morphimIdom GDx morphim_gen ?sub1set // morphim_set1 //.
by apply/cyclicP; exists (f x).
Qed.

Lemma ZgroupS : forall gT (G H : group gT),
  H \subset G -> Zgroup G -> Zgroup H. 
Proof.
rewrite/Zgroup; move=> gT G H HsubG; move/forallP=> zgG.
apply/forallP=> V; apply/implyP; case/is_sylowP=> p pr_p. 
rewrite sylowE; case/andP=> VsubH cardV. 
have exP: exists P : {group gT}, (V \subset P) && sylow p G P.
  by apply: sylow1_subset cardV; rewrite //; apply: (subset_trans VsubH).
case: exP=> P; case/andP=> VsubP sPG; apply: (cyclicS VsubP).
by apply: (implyP (zgG P)); apply /is_sylowP; exists p.
Qed.

Lemma Zgroup_morphim : forall (gT rT : finGroupType) (G D : group gT)
                              (f : {morphism D >-> rT}),
  Zgroup G -> Zgroup (f @* G). 
Proof.
move=> gT rt G D f. move/(ZgroupS (subsetIr D _)).
rewrite/Zgroup.
move/forallP=> zgG.
apply/forallP=> V; apply/implyP; case/is_sylowP=> p pr_p => spV.  
case: (sylow1_cor (D :&: G) pr_p) => P spP.
have cfP: cyclic (f @* P).
  by apply: cyclic_morphim; apply: (implyP (zgG P)); apply/is_sylowP; exists p.
have spfP: sylow p (f @* G) (f @* P).
  rewrite -morphimIdom; apply: morphim_sylow; rewrite //.
  by rewrite sylowE in spP; case/andP: spP; rewrite subsetI; case/andP.
by case (sylow2_cor pr_p spfP spV)=> x xin ->; rewrite -cyclicJ.
Qed.

Lemma Phi_char: forall gT (G : group gT), 'Phi(G) \char G. Admitted.

Lemma p_length_1_quo_p : forall p gT (G H : group gT),
  prime p -> H <| G -> trivg 'O_[~p] (G / H) ->
  p_length_1 p (G / H) -> p_length_1 p G.
Admitted.

Lemma p_length_1_quo2_p : forall p gT (G H N : group gT),
  prime p -> H <| G -> N <| G -> trivg (H :&: N) ->
  p_length_1 p (G / H) -> p_length_1 p (G / N) -> p_length_1 p G.
Admitted.

Lemma coprime_cent_Phi : forall gT (A G : group gT),
  coprime #|A| #|G| -> [~: A, G] \subset 'Phi(G) ->  A \subset 'C(G).
Admitted.

Lemma solvable_self_cent_Fitting : forall gT (G : group gT),
  solvable G -> 'C_G('F(G)) \subset 'F(G).
Admitted.

Lemma Fitting_normal : forall gT (G : group gT), 'F(G) <| G.
Admitted.

Theorem three_dot_six : forall (T : finGroupType) (G H R R0: {group T}),
    solvable G -> odd #|G| ->
    H <| G -> is_hall G H -> R \in complg G H ->
    R0 \subset R -> prime #|R0| -> Zgroup 'C_H(R0) ->
  forall p, prime p -> p_length_1 p [~: H, R].
Proof.
move=> T G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n T G => // n IHn T G; rewrite ltnS => leGn H R R0.
move=> solG oddG nHG hallH compH_R sR0R pR0. (* move oR0: #|R0| => r pr_r. *)
move=> ZCHR0 p ppr.
case/complgP: compH_R=> trivgHR eqHR_G; case/andP: (hallH) => sHG. 
rewrite -group_divn -eqHR_G ?mulG_subl //. 
rewrite (card_mulG_trivP _ _ trivgHR) ?divn_mulr ?pos_card_group // {trivgHR} => coHR.
have RnH: R \subset 'N(H). 
  by apply: (subset_trans _ (normal_norm nHG)); rewrite -eqHR_G mulG_subr.
have IHG: forall H1 R1 : {group T},
  H1 <| H -> R0 \subset R1 -> R1 \subset 'N_R(H1) ->
  #|H1| < #|H| \/ #|R1| < #|R| -> p_length_1 p [~: H1, R1].
  move=> H1 R1 nH1 sR01; rewrite subsetI; case/andP=> sR1R nH1R ltHR1.
  have sHR1_G: H1 <*> R1 \subset G.
    rewrite gen_subG subUset; apply/andP; split.
    - by apply: (subset_trans (normal_sub nH1) (normal_sub nHG)).
    - by apply: (subset_trans sR1R); rewrite -eqHR_G mulG_subr.
  have coHR1: coprime #|H1| #|R1|.
    rewrite /coprime; apply/eqP; apply: gcdn_def; rewrite ?dvd1n //.
    move=> d dH1 dR1; move: coHR; rewrite /coprime; move/eqP <-.
    apply: dvdn_gcd.
    - by apply: (dvdn_trans dH1); apply: group_dvdn; apply: (normal_sub nH1).
    - by apply: (dvdn_trans dR1); apply: group_dvdn. 
  have card_HR1: #|H1 <*> R1| = (#|H1| * #|R1|)%nat.
    by rewrite mulgenC norm_mulgenE // normC // coprime_card_mulG.
  have is_hall_HR1: is_hall (H1 <*> R1) H1.
    have sH1: H1 \subset (H1 <*> R1) by apply: (subset_trans _ (subset_gen _)); apply: subsetUl.
    by rewrite /is_hall sH1 // -group_divn //= ?card_HR1 ?divn_mulr ?pos_card_group ?mulg_subl //.
  have solvHR1: solvable (H1 <*> R1) by apply: solvable_sub solG.
  have odd_HR1: odd #|H1 <*> R1|.
    move: oddG; do 2!rewrite -[odd _]negbK -dvdn2_even; apply: contra. 
    move/dvdn_trans; apply; exact: group_dvdn.
  have compl_HR1: R1 \in complg (H1 <*> R1) H1.
    apply/complgP; split; first by apply: coprime_trivg.
    by rewrite /= mulgenC norm_mulgenE // -normC.
 have nH1gen: H1 <| H1 <*> R1.
   by rewrite /(H1 <| _) gen_subG subUset normG nH1R sub_gen ?subsetUl. 
 apply: (IHn T (H1 <*> R1)%G _ H1 R1 R0) => //.
    apply: leq_trans leGn.
    have leH1H := leqif_geq (subset_leq_card (normal_sub nH1)).
    have leR1R := leqif_geq (subset_leq_card sR1R).
    rewrite card_HR1 -eqHR_G coprime_card_mulG //.
    rewrite ltn_neqAle !(leqif_mul leH1H leR1R) andbT.
    rewrite negb_or negb_and -!ltnNge -lt0n ltn_0mul !ltn_0group /=.
    exact/orP.
  by apply: ZgroupS ZCHR0; rewrite setSI ?normal_sub.
without loss defHR: / [~: H, R] = H.
  have:= RnH; rewrite -subcomm_normal commsgC subEproper.
  case/predU1P=> [-> -> //|sHR_H _].
  have nHR_G:= normal_commutator H R.
  rewrite commGAA //; last exact: solvable_sub solG.
  apply: IHG => //; last by left; exact: proper_card.
    by apply: normalS nHR_G; rewrite ?sub_gen ?subsetUl ?proper_sub.
  rewrite subsetI subset_refl; apply: subset_trans (normal_norm nHR_G).
  by rewrite sub_gen ?subsetUr.
have{IHn hallH} IHquo: forall X : group T,
  ~~ trivg X -> X <| H -> R \subset 'N(X) -> p_length_1 p (H / X).
- move=> X ntX; case/andP=> sXH nXH nXR.
  rewrite -defHR quotientE morphimR // -!quotientE.
  have nXG: G \subset 'N(X) by rewrite -eqHR_G -['N(X)]mulGid mulgSS.
  have ltGx: #|G / X| < n.
    apply: leq_trans leGn; rewrite card_quotient //.
    rewrite -[#|G : X|]mul1n -(LaGrange (subset_trans sXH sHG)).
    by rewrite ltn_pmul2r // ltnNge -trivg_card.
  have pr_R0X: prime #|R0 / X|.
    rewrite (card_quotient (subset_trans sR0R nXR)). 
    rewrite -group_divnI [R0 :&: X](trivgP _ _) ?cards1 ?divn1 //.
    apply: subset_trans (coprime_trivg coHR); rewrite setIC.
    exact: subset_trans (setIS _ _) (setSI _ _).
  apply: (IHn _ _ ltGx) pr_R0X _ _ ppr => //.
  + exact: solvable_quo.
  + move: oddG; do 2!rewrite -[odd _]negbK -dvdn2_even; apply: contra. 
    move/dvdn_trans; apply; exact: dvdn_morphim.
  + exact: morphim_normal.
  + exact: morphim_is_hall.
  + apply/complgP; split; last by rewrite -morphimMl ?eqHR_G. 
    rewrite -morphimGI ?ker_coset //.
    by rewrite [H :&: R](trivgP _ (coprime_trivg coHR)) morphim1.
  + exact: morphimS.
  rewrite -coprime_quotient_cent_weak //; first exact: Zgroup_morphim.
  + exact/andP.
  + exact: subset_trans sR0R nXR.
  + by have:= coHR; rewrite -(LaGrange sR0R) coprime_mulr; case/andP.
  exact: solvable_sub solG.
rewrite defHR.
without loss Op'_H: / trivg 'O_[~ p](H).
  case/orP: (orbN (trivg 'O_[~ p](H))) => [-> -> // | ntO _].
  suffices: p_length_1 p (H / 'O_[~ p](H)) by admit.
  apply: IHquo => //; first exact: core_normal.
  apply: subset_trans (mulG_subr H R) (normal_norm _); rewrite eqHR_G.
  apply: char_norm_trans nHG; exact: char_core.
move defV: 'F(H)%G => V.
have defVp: V = 'O_[p](H) :> set _.
  admit.
have sCV_V: 'C_H(V) \subset V.
  rewrite -defV solvable_self_cent_Fitting //; exact: solvable_sub solG.
wlog abV: / abelem p V.
  case/orP: (orbN (trivg 'Phi(V))) => [trPhi -> // | ntPhi _].
    admit.
  have chPhi: 'Phi(V) \char H.
    rewrite defVp; exact: char_trans (Phi_char _) (char_core _ _).
  have nPhiH := normal_char chPhi.
  have{chPhi} nPhiR: R \subset 'N('Phi(V)).
    apply: subset_trans (mulG_subr H R) (normal_norm _); rewrite eqHR_G.
    exact: char_norm_trans nHG.
  apply: (p_length_1_quo_p ppr nPhiH); last exact: IHquo.
  have: 'O_[~p](H / 'Phi(V)) <| H / 'Phi(V) by exact: core_normal.
  case/(inv_quotientN _) => // W defW sPhiW nWH.
  suffices pW: pgroup p W.
    rewrite trivg_card (@pi_nat_1 (pred1 p) #|_|) //.
      by rewrite defW [pi_nat _ _]morphim_pi_group.
    by rewrite [pi'_nat _ _]pi_group_core.
  apply/pi_groupP=> q pr_q; case/cauchy=> // x; case/andP=> Wx; move/eqP=> oxq.
  have pV: pgroup p V by rewrite defVp /pgroup pi_group_core.
  apply/idPn=> /= neqp.
  suff: <[x]> \subset V.
    rewrite gen_subG sub1set => Vx.
    by move/pi_groupP: pV neqp => /= -> //; rewrite -oxq order_dvd_g.
  apply: subset_trans sCV_V; rewrite subsetI cycle_h /=; last first.
    apply: subsetP Wx; exact: normal_sub.
  have coxV: coprime #[x] #|V|.
    by rewrite oxq coprime_sym (pi_nat_coprime pV) // /pi'_nat pi_nat_prime.
  apply: coprime_cent_Phi coxV _.
  have: W :&: V \subset 'Phi(V); last apply: subset_trans.
    rewrite -trivg_quotient; last first.
      by rewrite subIset // orbC normal_norm // normal_char // Phi_char.  
    rewrite quotientE morphimIG ?ker_coset ?Phi_subset // -!quotientE.
    rewrite setIC coprime_trivg // (@pi_nat_coprime (pred1 p)) //.
      by rewrite [pi_nat _ _]morphim_pi_group.
    by rewrite -defW [pi'_nat _ _]pi_group_core.
  rewrite subsetI andbC subcomm_normal cycle_h; last first.
    apply: subsetP Wx; apply: (subset_trans (normal_sub nWH)).
    by rewrite defVp normal_norm ?core_normal.
  case/andP: nWH => _; rewrite -subcomm_normal commsgC; apply: subset_trans.
  by rewrite commgSS ?cycle_h // defVp normal_sub ?core_normal.
have{sCV_V} eqVC: V = 'C_H(V) :> (set _). 
  apply/eqP; rewrite eqset_sub sCV_V subsetI andbT; apply/andP; split.
    by rewrite defVp normal_sub ?core_normal.
  by case/andP: abV.
have sVH: V \subset H by rewrite eqVC subsetIl.
have sRG: R \subset G by rewrite -eqHR_G mulG_subr.
wlog nondecV:  / forall N1 N2,
      N1 \x N2 = V -> G \subset 'N(N1) :&: 'N(N2) -> trivg N1 \/ N1 = V.
  case: (pickP [pred N | [&& N.1 \x N.2 == V,
                              G \subset 'N(N.1) :&: 'N(N.2),
                             ~~ trivg N.1 & ~~ trivg N.2]]).
    case=> A1 A2 /=; case: eqP => //=.
    case/dprodGP=> [[N1 N2 -> ->{A1 A2} defN _] trN12].
    case/and3P; rewrite subsetI; case/andP=> nN1G nN2G ntN1 ntN2 _.
    have [nN1_H nN1_R]: N1 <| H /\ R \subset 'N(N1).
      apply/andP; rewrite /(_ <| H) (subset_trans _ sVH); last first.
        by rewrite -defN mulG_subl.
      by rewrite -subUset (subset_trans _ nN1G) // subUset sHG sRG.
    have [nN2_H nN2_R]: N2 <| H /\ R \subset 'N(N2).
      apply/andP; rewrite /(_ <| H) (subset_trans _ sVH); last first.
        by rewrite -defN mulG_subr.
      by rewrite -subUset (subset_trans _ nN2G) // subUset sHG sRG.
    apply: (p_length_1_quo2_p ppr nN1_H nN2_H trN12); exact: IHquo.
  move=> trN12; apply=> N1 N2 defN nNG; move/(_ (N1, N2)): trN12.
  rewrite /= defN eqxx {}nNG /= -negb_or; case/orP; first by left.
  case/dprodGP: defN => [] [_ N3 _ -> <- _] _; move/trivgP->.
  by right; rewrite mulg1.



; rewrite //=; apply: (subset_trans _ (normal_norm nN1)).
    rewrite -eqHR_G; apply: mulG_subr.
  - apply: IHquo; rewrite //=; apply: (subset_trans _ (normal_norm nN2)).
    rewrite -eqHR_G; apply: mulG_subr.
    

   #|[set N | [min N | ~~ trivg N && (N <| G)] && (N \subset V)]| = 1%N.

forallb N1 : {group T}, forallb N2 : {group T}, (N1 <| G) ==> (N1 \subset H) 
      ==> (N2 <| G) ==> (N2 \subset H) ==> trivg (N1 :&: N2) ==> (trivg N1 || trivg N2).
  case/orP: (orbN (forallb N1 : {group T}, forallb N2 : {group T}, (N1 <| G) ==> (N1 \subset H) 
    ==> (N2 <| G) ==> (N2 \subset H) ==> trivg (N1 :&: N2) ==> (trivg N1 || trivg N2)))=> [-> -> // | nn _].
  case/existsP:nn=>N1;case/existsP=>N2; rewrite !negb_imply.
  case/andP=> nN1; case/andP=> sN1;  case/andP=> nN2; case/andP=> sN2; case/andP => trivI.
  rewrite negb_orb; case/andP=> ntrivN1 ntrivN2.
  have nN1_H: N1 <| H.
    by rewrite/normal sN1 //=; apply: (subset_trans sHG); apply: (normal_norm nN1).
  have nN2_H: N2 <| H.
    by rewrite/normal sN2 //=; apply: (subset_trans sHG); apply: (normal_norm nN2).
  apply: (p_length_1_quo2_p ppr nN1_H nN2_H trivI). 
  - apply: IHquo; rewrite //=; apply: (subset_trans _ (normal_norm nN1)).
    rewrite -eqHR_G; apply: mulG_subr.
  - apply: IHquo; rewrite //=; apply: (subset_trans _ (normal_norm nN2)).
    rewrite -eqHR_G; apply: mulG_subr.

admit.
Qed.


