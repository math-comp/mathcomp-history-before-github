Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms normal commutators.
Require Import cyclic center pgroups sylow dirprod schurzass hall. 
Require Import coprime_act nilpotent coprime_comm.

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
Lemma ZgroupS : forall gT (G H : group gT),
  H \subset G -> Zgroup G -> Zgroup H. 
Admitted.
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
Lemma Zgroup_morphim : forall (gT rT : finGroupType) (G D : group gT)
                              (f : {morphism D >-> rT}),
  Zgroup G -> Zgroup (f @* G). 
Admitted.
  rewrite -coprime_quotient_cent_weak //; first exact: Zgroup_morphim.
  + exact/andP.
  + exact: subset_trans sR0R nXR.
  + by have:= coHR; rewrite -(LaGrange sR0R) coprime_mulr; case/andP.
  exact: solvable_sub solG.
rewrite defHR.
without loss Op'_H: / trivg 'O_[~ p](H).
  case/orP: (orbN (trivg 'O_[~ p](H))) => [-> -> // | ntO _].
  suffices: p_length_1 p (H / 'O_[~ p](H)). admit.
  apply: IHquo => //.
    simpl. have:= (core_normal (predC (pred1 p)) H).
    admit.
  admit.
admit.
Qed.


