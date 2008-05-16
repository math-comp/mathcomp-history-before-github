Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype paths.
Require Import connect div tuple finfun finset groups normal group_perm.
Require Import automorphism zp action normal sylow cyclic signperm.

Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.


(***************************************************************************)
(*                                                                         *)
(*                                                                         *)
(** Definitions of the alternate groups and some Properties                *)
(*                                                                         *)
(*                                                                         *)
(***************************************************************************)

Import GroupScope.

Section Alt.

Variable d : finType.

Notation Local oddp := (@odd_perm _ : pred {perm d}).

Lemma card_alt0 : #|d| <= 1 -> #|alt d| = 1%N.
move=> Hcard; have cardS : #|sym d| = 1%N.
  by rewrite card_sym; case: #|d| Hcard => [|[]].
apply/eqP; rewrite eqn_leq ltnNge leqn0 -lt0n pos_card_group.
by rewrite -cardS subset_leq_card // alt_subset.
Qed.

End Alt.

Lemma simple_alt_1 : forall d : finType, #|d| <= 3 -> simple (alt d).
Proof.
move=> d; rewrite leq_eqVlt; case/predU1P => Hcard; last first.
  have{Hcard} F1: #|alt d| = 1%N.
    move: Hcard; rewrite ltnS leq_eqVlt; case/predU1P; last exact: card_alt0.
    by move=> Hcard; apply/eqP; rewrite -(@eqn_pmul2l 2) // card_alt Hcard.
  apply/simpleP=> K; case/andP=> Hs _; left.  
  by rewrite (trivgP K _) ?trivg_card // -F1 subset_leq_card.
have F1: #|alt d| = 3 by apply/eqP; rewrite -(@eqn_pmul2l 2) // card_alt Hcard.
apply/simpleP=> /= K; case/andP=> sKH _.
have:= group_dvdn sKH; rewrite F1 dvdn_divisors // !inE orbF orbC -F1.
case/predU1P; first by right; apply/setP; exact/subset_cardP.
rewrite (cardD1 1) group1 eqSS [_ == _]disjoint_sym disjoint_subset => sK1.
left; rewrite {sKH} (trivgP K _) //; apply: subset_trans sK1 _.
by apply/subsetP=> x; rewrite !inE /= negbK.
Qed.


(* Un theoreme a deplacer dans group_perm *)
Lemma tpermD : forall (d : finType) (x y z : d),
  x != z -> y != z -> tperm x y z = z.
Proof. by move => d x y z; case tpermP => // ->; rewrite eqxx. Qed.

Lemma normal_sylowP : forall (gT : finGroupType) (G : {group gT}) p,
  prime p -> reflect (exists2 P : {group gT}, sylow p G P & P <| G)
                     (#|gsylow p G| == 1%N).
Proof.
move=> gT G p p_pr; apply: (iffP idP) => [syl1 | [P sylP nPG]].
  have [P sylP]: exists P, P \in gsylow p G.
    by apply/existsP; rewrite /pred0b (eqP syl1).
  exists P => //; apply/normalsubP; split=> [|x Gx]; first by case/andP: sylP.
  apply/eqP; apply/idPn=> nPxP.
  rewrite (cardD1 P) sylP eqSS in syl1; case/existsP: syl1.
  exists (P :^ x)%G; rewrite /= nPxP -topredE /gsylow /=.
  by rewrite -(conjGid Gx) -sylow_sconjg.
rewrite (cardD1 P) [P \in _]sylP eqSS; apply/pred0P=> Q /=.
apply/andP=> [[nQP sylQ]]; case/eqP: nQP; apply: val_inj=> /=.
case: (sylow2_cor p_pr sylP sylQ) => x [Gx ->{Q sylQ}].
case/normalsubP: nPG => _; exact.
Qed.

Lemma not_simple_alt_4: forall d : finType, #|d| = 4 -> ~~ simple (alt d).
Proof.
move => d card_d; set A := alt d : set _.
have cA: #|A| = 12 by apply: double_inj; rewrite -mul2n card_alt card_d.
have [p [p_pr pA_int Sp1]]:
  exists p, [/\ prime p, 1 < p_part p #|A| < #|A| & #|gsylow p A| == 1%N].
- pose Syl3 := set_of (gsylow 3 A).
  have: #|Syl3| \in filter [pred d | d %% 3 == 1%N] (divisors 12).
    rewrite mem_filter -dvdn_divisors //= -cA cardsE.
    by rewrite sylow3_div ?sylow3_mod.
  rewrite /= cA; case/orP; first by rewrite cardsE; exists 3.
  case/predU1P=> //; move/(congr1 double).
  pose Q3 := \bigcup_(Q \in Syl3) (Q :\ 1).
  have <-: #|Q3| = #|Syl3|.*2.
    rewrite -muln2; apply: card_setnU_id => /= [Q1 Q2 x | Q]; last first.
      by rewrite inE; case/andP=> _; rewrite (cardsD1 1) group1 cA; case/eqP.
    rewrite /= !{1}inE; case/andP=> _; rewrite cA -[_ 3 _]/3; move/eqP=> cQ1.
    case/andP=> _; rewrite cA -[_ 3 _]/3; move/eqP=> cQ2.
    case/andP=> nx1 Q1x; rewrite nx1 /= => Q2x.
    apply: val_inj; apply/setP; apply/subset_cardP; first by rewrite cQ1.
    have sQ12: Q1 :&: Q2 \subset Q1 by exact: subsetIl.
    rewrite -eqsetIl /= eqset_sub_card sQ12 leq_eqVlt eq_sym; apply/orP; left.
    have:= group_dvdn sQ12; rewrite cQ1 dvdn_divisors // -topredE /= orbF.
    case/orP=> //; rewrite (cardD1 1) group1 eqSS; case/existsP.
    by exists x; rewrite /= inE nx1 Q1x.
  move=> /= cQ3; pose Syl2 := gsylow 2 A.
  have{cQ3} nQS2: forall P, P \in Syl2 -> P = A :\: Q3 :> set _.
    move=> P; case/andP=> sAP; rewrite cA -[_ 2 _]/4; move/eqP=> cP.
    apply/setP; apply/subset_cardP.
      apply: (@addn_injl #|A :&: Q3|); rewrite cardsID cA cP addnC; congr _.+4.
      rewrite -[8]cQ3; congr #|_ : set _|; apply/eqP; rewrite setIC eqsetIl.
      apply/subsetP=> x; case/bigcupP=> Q; rewrite 2!inE; case/andP=> sAQ _.
      case/andP=> _; exact: (subsetP sAQ).
    apply/subsetP=> x Px; rewrite inE (subsetP sAP) // andbT.
    apply/bigcupP=> [[Q]]; rewrite !inE; case/andP=> _.
    rewrite cA -[_ 3 _]/3; move/eqP=> cQ; case/andP=> nx1 Qx.
    have sPQP: P :&: Q \subset Q by exact: subsetIr.
    have:= (group_dvdn sPQP); rewrite cQ dvdn_divisors //= !inE orbF.
    rewrite {1}(cardD1 1) (cardD1 x) group1 inE [_ x]/= inE nx1 Px Qx /= -cQ.
    move/eqP=> cPQ; move/(subset_cardP cPQ): sPQP; move/setP; move/eqP.
    by rewrite setIC eqsetIl; move/group_dvdn; rewrite cP cQ.
  case: ((sylow1_cor [group of A]) 2) => //= P sylP; exists 2; split => //.
  rewrite (cardD1 P) [P \in _]sylP eqSS; apply/pred0P=> P'.
  apply/andP=> [[nPP' sylP']]; case/eqP: nPP'.
  by apply: val_inj; rewrite /= !nQS2.
case: (normal_sylowP (alt d) p_pr Sp1) => P; case/andP=> sPA sylP nPA.
rewrite -[_ p _](eqP sylP) in pA_int.
by apply/simpleP; case/(_ P)=> // defP; rewrite defP cA ?cards1 in pA_int.
Qed.

Module alt_CP_1. End alt_CP_1.

(* trivial proof *)
Notation Local tp := is_true_true.

Lemma normal_stab: forall gT sT (to : action gT sT) (H1 H2 : {group _}) a, 
  H2 \subset'N(H1) -> stabilizer to H2 a \subset 'N(stabilizer to H1 a).
Proof.
move=> gT sT to H1 H2 a Hnorm.
apply/subsetP => g; case/stabilizerP => Hg Hperm.
rewrite /normaliser inE; apply/subsetP => g1 /=.
rewrite mem_conjg; case/stabilizerP => Hg1 Hperm1.
apply/stabilizerP; split.
by move/normalP: Hnorm; move/(_ g Hg) => <-; rewrite mem_conjg.
move: Hperm1; rewrite !actM invgK Hperm -actM => Hperm1.
by rewrite -{2}Hperm -{2}Hperm1 -!actM; gsimpl.
Qed.

Lemma simple_alt5_base: forall d : finType, #|d| = 5 -> simple (alt d).
Proof.
move=> d Hd.
have F1: #|alt d| = 60 by apply: double_inj; rewrite -mul2n card_alt Hd.
have FF: forall H : group _, H <| alt d -> H <> 1 :> set _ -> 20 %| #|H|.
- move=> H Hh1 Hh3.
  have [x _]: exists x, x \in d by apply/existsP; rewrite /pred0b Hd.
  have F2 := alt_trans d; rewrite Hd in F2.
  have F3 := ntransitive1 (tp: 0 < 3) F2.
  have F4 := ntransitive_primitive (tp: 1 < 3) F2.
  case: (prim_trans_norm F3 F4 Hh1) => F5.
    case: Hh3; apply/setP=> z; rewrite /= inE.
    apply/idP/eqP=> Hz; last by rewrite Hz group1.
    apply/eqP; move: (perm_action_faithful d); rewrite /faithful.
    rewrite (cardD1 1) akernel1; move/pred0P; move/(_ z)=> /=.
    by rewrite (subsetP F5) // andbT; move/eqP->.
  have F6: 5 %| #|H| by rewrite -Hd; exact: trans_div (x) _ _ F5. 
  have F7: 4 %| #|H|.
    have F7: #|predD1 d x| = 4 by rewrite (cardD1 x) in Hd; case: Hd.
    case E1: (pred0b (predD1 d x)); first by rewrite /pred0b F7 in E1.
    case/pred0Pn: E1 => y Hy.
    pose K := group_stab (perm_action d) H x.
    have F8: K \subset H by apply: subset_stab.
    pose Gx := group_stab (perm_action d) (alt d) x.
    have F9: ntransitive (perm_action d) Gx (predD1 d x) (3 - 1).
      exact: stab_ntransitive.
    have F10: transitive (perm_action d) Gx (predD1 d x).
      exact: ntransitive1 F9.
    have F11: primitive (perm_action d) Gx (predD1 d x).
      exact: ntransitive_primitive F9.
    have F12: K \subset Gx.
      apply/subsetP=> g; case/stabilizerP => Hg Hperm.
      apply/stabilizerP; split => //; case/andP: Hh1 => sH1 _.
      exact: (subsetP sH1).
    have F13: K <| Gx.
      by apply/andP; split=> //; apply: normal_stab; case/andP: Hh1.
    case: (prim_trans_norm F10 F11 F13) => Ksub; last first.
      apply: dvdn_trans (group_dvdn F8). 
      by rewrite -F7; apply: (@trans_div _ _ (perm_action d) _ _ _ Hy).
    have F14: faithful (perm_action d) Gx (predD1 d x).
      apply/faithfulP => g Hg.
      apply: (faithfulP _ _ _ (perm_action_faithful d)) => z Hz.
      case: (Hg _ Hy); case/stabilizerP => Hag Hx1 Hy1; split => //.
      case E1: (x == z); first by rewrite -(eqP E1).
      by case: (Hg z); rewrite // inE /= eq_sym E1.
    have Hreg: forall g (z : d), g \in H -> g z = z -> g = 1.
      have F15: forall g, g \in H -> g x = x -> g = 1.
        move => g Hg Hgx.
        have F15: #|K| <= 1.
          rewrite /faithful /= in F14; rewrite -(eqP F14).
          by apply: subset_leq_card.
        have F16: g \in K by apply/stabilizerP.
        move: F15; rewrite (cardD1 1) group1 ltnS leqn0; move/pred0P.
        by move/(_ g); rewrite /= F16 andbT; move/eqP->.
      move=> g z Hg Hgz.
      have:= F3 z tp x; case/imsetP => g1 Hg1 Hg2.
      apply: (conjg_inj g1); rewrite conj1g.
      apply: F15.
        by case/normalsubP: Hh1 => _ nH1; rewrite -(nH1 _ Hg1) memJ_conjg.
      by rewrite Hg2 -permM mulKVg permM Hgz.
    clear K F8 F12 F13 Ksub F14.
    case: (cauchy (tp: prime 5) F6) => h; case/andP => Hh Horder.
    have diff_hnx_x: forall n, 0 < n -> n < 5 -> x != (h ^+ n) x.
      move=> n Hn1 Hn2; rewrite eq_sym; apply/negP => HH.
      have: #[h ^+ n] = 5.
        rewrite orderg_gcd // /orderg (eqP Horder).
        by move: Hn1 Hn2 {HH}; do 5 (case: n => [|n] //).
      have Hhd2: h ^+ n \in H by rewrite groupX.
      by rewrite (Hreg _ _ Hhd2 (eqP HH)) orderg1.
    pose S1 := [tuple x; h x; (h ^+ 3) x].
    have DnS1: dtuple_on d S1.
      rewrite -[dtuple_on _ _]andbA -!andbA !(negb_or, andbT, diff_hnx_x) //.
      rewrite -{1}[h]expg1 diff_hnx_x // -addn1 expgn_add permM expg1.
      by rewrite (inj_eq (@perm_inj _ _)) diff_hnx_x.
    pose S2 := [tuple x; h x; (h ^+ 2) x].
    have DnS2:  dtuple_on d S2.
      rewrite -[dtuple_on _ _]andbA -!andbA !(negb_or, andbT, diff_hnx_x) //.
      by rewrite permM mulg1 (inj_eq (@perm_inj _ _)) -[h]expg1 diff_hnx_x.
    case: F2 => F2 Fc.
    rewrite -[_ S2](F2 _ DnS1) in DnS2; case/imsetP: DnS2 => g Hg.
    case/(congr1 val); rewrite /perm_to => Hgx Hghx Hgh3x.
    have h_g_com: h * g = g * h.
      suff HH: (g * h * g^-1) * h^-1 = 1 by rewrite -[h * g]mul1g -HH; gsimpl.
      apply: (Hreg _ x); last first.
        by rewrite !permM -Hgx Hghx -!permM mulKVg mulgV perm1.
      rewrite groupM // ?groupV // (conjgCV g) mulgK -mem_conjg.
      by case/normalsubP: Hh1 => _ ->.
    have: (g * (h ^+ 2) * g ^-1) x = (h ^+ 3) x.
      rewrite !permM !perm1 -Hgx.
      have ->: h (h x) = (h ^+ 2) x by rewrite /= permM mulg1.
      by rewrite {1}Hgh3x -!permM /= mulgV mulg1 -expgSr.
    rewrite commuteX // mulgK {1}[expgn]lock expgS permM -lock.
    by move/perm_inj=> eqxhx; case/eqP: (diff_hnx_x 1%N tp tp); rewrite expg1.
  by rewrite (@gauss_inv 4 5) // F7.
apply/simpleP=> H Hnorm.
case Hcard1: (#|H| == 1%N); move/eqP: Hcard1 => Hcard1.
  left; apply/setP.
  apply: fsym; apply/subset_cardP; first by rewrite cards1.
  by apply/subsetP => z; rewrite inE; move/eqP->; exact: group1.
right; case Hcard60: (#|H| == 60%N); move/eqP: Hcard60 => Hcard60.
  by apply/eqP; rewrite eqset_sub_card Hcard60 F1 andbT; case/andP: Hnorm.
have Hcard20: #|H| = 20; last clear Hcard1 Hcard60.
  have Hdiv: 20 %| #|H| by apply: FF => // HH; case Hcard1; rewrite HH cards1.
  case H20: (#|H| == 20); first by apply/eqP.
  case: Hcard60; case/andP: Hnorm; move/group_dvdn; rewrite F1 => Hdiv1 _.
  by case/dvdnP: Hdiv H20 Hdiv1 => n ->; move: n; do 4!case=> //.
have prime_5: prime 5 by [].
have nSyl5: #|gsylow 5 H| = 1%N.
  move: (sylow3_div H prime_5) (sylow3_mod H prime_5).
  rewrite Hcard20; case: (card _) => // n Hdiv.
  move: (dvdn_leq  (tp: (0 < 20)%N) Hdiv).
  by move: (n) Hdiv; do 20 (case => //).
case: (sylow1_cor H prime_5) => S; case/andP=> sSH oS.
have{oS} oS: #|S| = 5 by move/eqP: oS; rewrite Hcard20. 
suff: 20 %| #|S| by rewrite oS.
apply FF => [|S1]; last by rewrite S1 cards1 in oS.
apply: char_norm_trans Hnorm; apply: (lone_subgroup_char sSH oS) => Q sQH oQ.
apply/eqP; apply/idPn=> nQS; move: nSyl5.
rewrite (cardD1 S) (cardD1 Q) -!topredE {1 2}/gsylow /= nQS /sylow Hcard20.
by rewrite sSH oS -topredE /= sQH oQ.
Qed.

Module alt_CP_2. End alt_CP_2.

Section Restrict.

Variable d : finType.
Variable x : d.
Let d' := sig_finType (xpredC1 x).

Lemma rfd_funP : forall (p : {perm d}) (u : d'),
  let p1 := if p x == x then p else 1 in predC1 x (p1 (val u)).
Proof.
move=> p u /=; case: (p x =P x) => [pxx|_]; last by rewrite perm1 (valP u).
apply: contra (valP u); move/eqP=> eq_pux.
by rewrite -(inj_eq (@perm_inj _ p)) eq_pux pxx.
Qed.

Definition rfd_fun p := [fun u => exist (xpredC1 x) _ (rfd_funP p u) : d'].

Lemma rfdP : forall p, injective (rfd_fun p).
Proof.
move=> p; apply: can_inj (rfd_fun p^-1) _ => u; apply: val_inj => /=.
rewrite (canF_eq (permKV p)) eq_sym.
by case: eqP => _; rewrite !(perm1, permK).
Qed.

Definition rfd p := perm_of (@rfdP p).

Lemma rfd1: rfd 1 = 1.
Proof.
by apply/permP => u; apply: val_inj; rewrite permE /= if_same !perm1.
Qed.

Lemma rfd_not_fp : forall p : {perm d}, p x != x -> rfd p = 1.
Proof.
move=> p; move/negPf=> npxx; apply/permP => u; apply: val_inj.
by rewrite permE /= npxx !perm1.
Qed.

Hypothesis card_d: 2 < #|d|.

Lemma rfd_dom: dom rfd = stabilizer (perm_action d) (setT_group _) x.
Proof.
apply/setP => p; apply/setUP/stabilizerP.
  move=> p_dom; split; first by rewrite inE.
  apply/eqP; apply/idPn=> npxx.
  case p_dom; last by rewrite inE rfd_not_fp ?eqxx.
  have [y nyx nypx]: exists2 y, y != x & y != p x.
    have:= card_d; rewrite (cardD1 x) (cardD1 (p x)) !inE /= npxx.
    by rewrite !ltnS lt0n; case/pred0Pn=> y; case/and3P=> /=; exists y.
   move/kerP => kerH.
  have xppx: x = p (p x).
    apply: (inv_inj (tpermK x (p x))); apply/eqP.
    move: (kerH (tperm x (p x))).
    rewrite [rfd (tperm _ _)]rfd_not_fp; last by rewrite tpermL.
    move/(congr1 (fun q : perm d' => q (exist (xpredC1 x) _ npxx))).
    rewrite perm1 permE; move/val_eqP.
    by rewrite /= !permM tpermR eq_refl permM eq_sym tpermL.
  move: (kerH (tperm x (p x) * (tperm (p x) y))).
  rewrite [rfd (tperm _ _ * _)]rfd_not_fp;  last first.
    by rewrite permM tpermL tpermL.
  have npmxx: p^-1 x != x by rewrite eq_sym -(canF_eq (permK p)).
  move/(congr1 (fun q : {perm d'} => q (exist (xpredC1 x) _ npmxx))).
  rewrite permE perm1; move/val_eqP=> /=.
  rewrite !permM tpermR tpermD ?eqxx //.
  rewrite !permM permKV tpermL tpermL => ypmx.
  by case/negP: nypx; rewrite (eqP ypmx) {1}xppx permK.
case=> _ Hx; rewrite inE.
case: (_ =P _) => E0; last by right.
suff ->: p = 1 by left; apply/kerP=> y; rewrite mul1g.
apply/permP => z; rewrite perm1.
case (z =P x) => [-> //|]; move/eqP => nzx; apply/eqP.
move: (congr1 (fun q : perm d' => q (exist (xpredC1 x) _ nzx)) E0).
by rewrite permE perm1; move/val_eqP => /=; rewrite -{2}Hx eq_refl.
Qed.

Definition rfd_morph: morphism (perm_finGroupType d) (perm_finGroupType d').
exists rfd.
  rewrite rfd_dom.
  exact: (@group_set_stab _ _ (perm_action d) (setT_group (perm_finGroupType d))).
move=> x1 y1; rewrite rfd_dom; case/stabilizerP=> _ Hx1.
case/stabilizerP=> _ Hy1.
rewrite /perm_action /perm_to /= in Hx1 Hy1.
have Hxy1: (x1 * y1) x = x by rewrite permM Hx1.
apply/permP => z.
by apply/val_eqP; rewrite permM ![rfd _ _]permE /= Hx1 Hy1 Hxy1 !eq_refl permM.
Defined.

Definition rgd_fun (p : {perm d'}) :=
  [fun x1 => if insub x1 is Some u then val (p u) else x].

Lemma rgdP : forall p, injective (rgd_fun p).
Proof.
move=> p; apply: can_inj (rgd_fun p^-1) _ => y /=.
case: (insubP _ y) => [u _ val_u|]; first by rewrite valK permK.
by rewrite negbK; move/eqP->; rewrite insubF //= eqxx.
Qed.

Definition rgd p := perm_of (@rgdP p).

Lemma rgd_x: forall p, rgd p x = x.
Proof. by move=> p; rewrite permE /= insubF //= eqxx. Qed.

Lemma rfd_rgd: forall p, rfd (rgd p) = p.
Proof.
move=> p; apply/permP => [[z Hz]]; apply/val_eqP; rewrite !permE.
rewrite /= [rgd _ _]permE /=.
rewrite insubF eq_refl // permE /=.
by rewrite (@insubT _ (xpredC1 x) _ _ Hz).
Qed.

Lemma rfd_odd : forall p: {perm d}, p x = x -> rfd p = p :> bool.
Proof.
have HP0: forall p : {perm d},
  #|[set x | p x != x]| = 0 -> rfd p = p :> bool.
- move => p Hp; suff ->: p = 1 by rewrite rfd1 !odd_perm1.
  apply/permP => z; rewrite perm1.
  suff: z \in [set x | p x != x] = false; first by rewrite inE; move/eqP.
  by rewrite (card0_eq Hp).
move=> p; elim: #|_| {-2}p (leqnn #|[set x | p x != x]|) => {p}[| n Hrec] p Hp Hpx.
  by apply: HP0; move: Hp; case: card.
case Ex: (pred0b (mem [set x | p x != x])); first by apply: HP0; move: Ex; rewrite /pred0b; move/eqP.
case/pred0Pn: Ex => x1; rewrite /= inE => Hx1.
have nx1x:  x1 != x by apply/eqP => HH; rewrite HH Hpx eqxx in Hx1.
have npxx1: p x != x1 by apply/eqP => HH; rewrite -HH !Hpx eqxx in Hx1.
have npx1x: p x1 != x.
  by apply/eqP; rewrite -Hpx; move/perm_inj => HH; case/eqP: nx1x.
pose p1 := p * tperm x1 (p x1).
have Hp1: p1 x = x.
  by rewrite /p1 permM; case tpermP => // [<-|]; [rewrite Hpx | move/perm_inj].
have Hcp1: #|[set x | p1 x != x]| <= n.
  have F1: forall y, p y = y -> p1 y = y.
    move=> y Hy; rewrite /p1 permM Hy.
    case tpermP => //; first by move => <-.
    by move=> Hpx1; apply: (@perm_inj _ p); rewrite -Hpx1.  
  have F2: p1 x1 = x1 by rewrite /p1 permM tpermR.
  have F3: [set x | p1 x != x] \subset [predD1 [set x | p x != x] & x1].
    apply/subsetP => z; rewrite !inE permM /= inE.
    case tpermP => HH1 HH2.
    - rewrite eq_sym HH1 andbb; apply/eqP=> dx1.
      by rewrite dx1 HH1 dx1 eqxx in HH2.
    - by rewrite (perm_inj HH1) eqxx in HH2.
    by move->; rewrite andbT; apply/eqP => HH3; rewrite HH3 in HH2.
  apply: (leq_trans (subset_leq_card F3)).
  by move: Hp; rewrite (cardD1 x1) inE Hx1.
have ->: p = p1 * tperm x1 (p x1) by rewrite -mulgA tperm2 mulg1.
rewrite odd_permM odd_tperm eq_sym Hx1.
rewrite (@morphM _ _ (rfd_morph)) ?rfd_dom /=; last 2 first.
- by apply/stabilizerP; rewrite inE.
- apply/stabilizerP; rewrite inE; split=> //.
  by rewrite -{1}Hpx /= -[perm_to _ _]permM.
rewrite odd_permM Hrec //; congr (_ (+) _).
pose x2: d' := exist (xpredC1 x) _ nx1x.
pose px2: d' := exist (xpredC1 x) _ npx1x.
suff ->: rfd (tperm x1 (p x1)) = tperm x2 px2.
  rewrite odd_tperm /x2 /px2; apply/eqP; move/val_eqP => /=.
  by rewrite eq_sym => HH; case/negP: Hx1.
apply/permP => z; apply/val_eqP; rewrite permE /= tpermD // eqxx.
case: (tpermP x2) => [->|->|HH1 HH2]; rewrite /x2 (tpermL, tpermR, tpermD) //.
  by apply/eqP=> HH3; case: HH1; apply: val_inj.
by apply/eqP => HH3; case: HH2; apply: val_inj.
Qed.

Lemma rfd_iso: isog (stabilizer (perm_action d) (alt d) x) (alt d').
Proof.
exists rfd_morph.
apply/andP; split.
  apply/eqP; apply/setP=> z; apply/imsetP/idP.
    case=> p; case/stabilizerP; move/altP => Hp Hp1 ->; apply/altP.
    by rewrite /even_perm rfd_odd.
  move=> Hz; exists (rgd z); last by rewrite /= rfd_rgd.
  apply/stabilizerP; split.
    apply/altP; rewrite /even_perm -rfd_odd ?rgd_x //.
    by rewrite rfd_rgd; case/altP: Hz.
  by rewrite /= /perm_to rgd_x. 
apply/injmP=> x1 y1.
case/stabilizerP=> Hax1 Hx1; case/stabilizerP=> Hay1 Hy1 /= Hr.
rewrite /perm_action /perm_to /= in Hx1 Hy1.
apply/permP => z.
case (z =P x) => [->|]; [by rewrite Hx1 | move/eqP => nzx].
move: (congr1 (fun q : perm d' => q (exist (xpredC1 x) _ nzx)) Hr).
by rewrite !permE; move/val_eqP; rewrite /= Hx1 Hy1 !eqxx; move/eqP.
Qed.

End Restrict.

Module alt_CP_3. End alt_CP_3.

Lemma simple_alt5 : forall d : finType, #|d| >= 5 -> simple (alt d).
Proof.
suff F1: forall n (d : finType), #|d| = n + 5 -> simple (alt d).
  move=> d H; apply: (F1 (#|d| - 5)).
  by rewrite addnC subnK.
elim => [| n Hrec d Hde]; first exact: simple_alt5_base.
have Hd: 5 < #|d| by rewrite Hde addnC.
apply/simpleP => H Hnorm; case: (andP Hnorm) => Hh1 nH.
case E1: (pred0b d); first by rewrite /pred0b in E1; rewrite (eqP E1) in Hd.
case/pred0Pn: E1 => x Hx.
have F2: ntransitive (perm_action d) (alt d) d 4.
  apply: ntransitive_weak (alt_trans d).
  by apply: (@ltn_sub2r 2 5) => //; apply: ltn_trans Hd.
have F3 := ntransitive1 (tp: 0 < 4) F2.
have F4 := ntransitive_primitive (tp: 1 < 4) F2.
case Hcard1: (#|H| == 1%N); move/eqP: Hcard1 => Hcard1.
  left; apply/setP; apply: fsym; apply/subset_cardP; first by rewrite cards1.
  by apply/subsetP => z; rewrite inE; move/eqP->; exact: group1.
right; case: (prim_trans_norm F3 F4 Hnorm) => F5.
  move: (perm_action_faithful d); rewrite /faithful; move/eqP => FC.
  by case: Hcard1; apply/eqP; rewrite eqn_leq -{1}FC subset_leq_card // (cardD1 1) group1.
case E1: (pred0b (predD1 d x)).
  rewrite /pred0b in E1; move: Hd.
  by rewrite (cardD1 x) (eqP E1); case: (d x).
case/pred0Pn: E1 => y Hdy; case/andP: (Hdy) => diff_x_y Hy.
pose K := stabilizer (perm_action d) H x.
have F8: K \subset H by apply: subset_stab.
pose Gx := group_stab (perm_action d) (alt d) x.
have F9: ntransitive (perm_action d) Gx (predD1 d x) (4 - 1) by apply:  stab_ntransitive.
have F10: transitive (perm_action d) Gx (predD1 d x).
 by apply:  (ntransitive1 (refl_equal true: 0 < 3)).
have F11: primitive (perm_action d) Gx (predD1 d x)
  by apply: (ntransitive_primitive (refl_equal true: 1 < 3)).
have F12: K \subset Gx.
  apply/subsetP=> g; case/stabilizerP => Hg Hperm.
  by apply/stabilizerP; split => //; apply: (subsetP Hh1).
have F13: K <| Gx by apply/andP; split; last apply: normal_stab.
case: (@prim_trans_norm _ _ _ {Gx as group _} _ F10 {K as group _} F11 F13) => Ksub; last first.
  have F14 := (subgroup_transitive Hx Hh1 F3 F5); rewrite -/Gx in F14.
  have Gx_simpl: simple Gx.
    have FF: 2 < #|d| by apply: (leq_trans _ Hd).
    apply: (isog_simpl (isog_sym (rfd_iso x FF))).
    apply: Hrec => /=; apply/eqP.
    by move/eqP: Hde; rewrite card_sub -(cardC (pred1 x)) card1 !addSn add0n.
  move/simpleP: Gx_simpl;move/(_ {K as group _} F13); case => HH2.
    case Ez: (pred0b (predD1 (predD1 d x) y)).
      move: Hd; rewrite /pred0b in Ez.
      by rewrite (cardD1 x) (cardD1 y) (eqP Ez) inE /= inE /= diff_x_y.  
    case/pred0Pn: Ez => z; case/andP => diff_y_z Hdz; case/andP: (Hdz) => diff_x_z Hz.
    move: Hdz; rewrite topredE -(Ksub _ Hdy); case/imsetP => g.
    rewrite HH2 inE; move/eqP => -> HH4.
    by case/negP: diff_y_z; rewrite HH4 act1.
  rewrite -F14; apply/setP; apply/subset_eqP; apply/andP; split; apply/subsetP => z.
    by move => Hz; apply/mulsgP; exists (1 : {perm d}) z; rewrite ?group1 // mul1g.
  case/mulsgP => t u Ht Hu ->; rewrite groupM // (subsetP F8) //. 
  by have: t \in Gx; rewrite // -HH2.
have F14: faithful (perm_action d) Gx (predD1 d x).
  apply/faithfulP => g Hg.
  apply: (faithfulP _ _ _ (perm_action_faithful d)) => z Hz.
  case: (Hg _ Hdy); case/stabilizerP => Hag Hx1 Hy1; split => //.
  case E1: (x == z); first by rewrite -(eqP E1).
  by case: (Hg z); rewrite // inE /= eq_sym E1.
have Hreg: forall g (z: d), g \in H -> g z = z -> g = 1.
  have F15: forall g, g \in H -> g x = x -> g = 1.
    move => g Hg Hgx.
    have F15: #|K| <= 1.
      rewrite /faithful /= in F14; rewrite -(eqP F14).
      by apply: subset_leq_card.
    have F16: g \in K by  apply/stabilizerP; split.
    by move: F15; rewrite (cardD1 1) group1 (cardD1 g) inE /= F16; case: eqP.
  move=> g z Hg Hgz.
  have:= F3 z tp x; case/imsetP=> g1 Hg1 Hg2.
  apply: (mulg_injl g1^-1); apply: (mulg_injr g1); gsimpl.
  apply: F15; first by rewrite -mulgA -(normalP nH _ Hg1) memJ_conjg.
  change (perm_action d x (g1^-1 * g * g1) = x).
  by rewrite Hg2 -actM; gsimpl; rewrite actM {2}/perm_action  /perm_to /= Hgz.
clear K F8 F12 F13 Ksub F14.
have Hcard: 5 < #|H|.
  apply: (leq_trans Hd); apply dvdn_leq; first by exact: pos_card_group.
  apply: (trans_div Hx F5).
case Eh: (pred0b [predD1 H & 1]).
  by move: Hcard; rewrite /pred0b in Eh; rewrite (cardD1 1) group1 (eqP Eh).
case/pred0Pn: Eh => h; case/andP => diff_1_h /= Hh.
case Eg: (pred0b (predD1 (predD1 [predD1 H & 1] h) h^-1)).
  move: Hcard; rewrite /pred0b in Eg.
  rewrite (cardD1 1) group1 (cardD1 h) (cardD1 h^-1) inE /= diff_1_h Hh.
  by rewrite (eqP Eg); case: (_ \in _).
case/pred0Pn: Eg => g; case/andP => diff_h1_g; case/andP => diff_h_g.
case/andP => diff_1_g /= Hg.
case diff_hx_x: (h x == x).
  by case/negP: diff_1_h; apply/eqP; apply: (Hreg _ _ Hh (eqP diff_hx_x)).
case diff_gx_x: (g x == x).
  case/negP: diff_1_g; apply/eqP; apply: (Hreg _ _ Hg (eqP diff_gx_x)).
case diff_gx_hx: (g x == h x).
  case/negP: diff_h_g; apply/eqP; symmetry; apply: (mulg_injr g^-1); gsimpl.
  apply: (Hreg _ x); first by rewrite groupM // groupV.
  by rewrite permM -(eqP diff_gx_hx) -permM mulgV perm1.
case diff_hgx_x: ((h * g) x == x).
  case/negP: diff_h1_g; apply/eqP; apply: (mulg_injl h); gsimpl.
  by apply: (Hreg _ x); first (by exact: groupM); apply/eqP.
case diff_hgx_hx: ((h * g) x == h x).
  case/negP: diff_1_g; apply/eqP.
  by apply: (Hreg _ (h x)) => //; apply/eqP; rewrite -permM.
case diff_hgx_gx: ((h * g) x == g x).
  case/eqP: diff_hx_x; apply: (@perm_inj _ g) => //.
  by apply/eqP; rewrite -permM.
case Ez: (pred0b
            (predD1 (predD1 (predD1 (predD1 d x) (h x)) (g x)) ((h * g) x))).
- move: Hd; rewrite /pred0b in Ez.
  rewrite (cardD1 x) (cardD1 (h x)) (cardD1 (g x)) (cardD1 ((h * g) x)).
  by rewrite (eqP Ez); do 3!case: (_ x \in _).
case/pred0Pn: Ez => z.
case/and5P=> diff_hgx_z diff_gx_z diff_hx_z diff_x_z /= Hz.
pose S1 := [tuple x; h x; g x; z].
have DnS1: dtuple_on d S1.
  rewrite -[dtuple_on _ _]andbA -!andbA !negb_or !andbT.
  rewrite -!(eq_sym z) diff_gx_z diff_x_z diff_hx_z.
  by rewrite !(eq_sym x) diff_hx_x diff_gx_x eq_sym diff_gx_hx.
pose S2 := [tuple x; h x; g x; (h * g) x].
have DnS2: dtuple_on d S2.
  rewrite -[dtuple_on _ _]andbA -!andbA !negb_or !andbT !(eq_sym x).
  rewrite diff_hx_x diff_gx_x diff_hgx_x.
  by rewrite !(eq_sym (h x)) diff_gx_hx diff_hgx_hx eq_sym diff_hgx_gx.
case: F2 => F2 Fc.
rewrite -[dtuple_on d S2](F2 _ DnS1) in DnS2; case/imsetP: DnS2 => k Hk.
case/(congr1 val); rewrite /perm_to => Hkx Hkhx Hkgx Hkhgx.
have h_k_com: h * k = k * h.
  suff HH: (k * h * k^-1) * h^-1 = 1 by rewrite -[h * k]mul1g -HH; gsimpl.
  apply: (Hreg _ x); last first.
    by rewrite !permM -Hkx Hkhx -!permM mulKVg mulgV perm1.
  by rewrite groupM // ?groupV // (conjgCV k) mulgK -mem_conjg (normalP nH).
have g_k_com: g * k = k * g.
  suff HH: (k * g * k^-1) * g^-1 = 1 by rewrite -[g * k]mul1g -HH; gsimpl.
  apply: (Hreg _ x); last first.
    by rewrite !permM -Hkx Hkgx -!permM mulKVg mulgV perm1.
  by rewrite groupM // ?groupV // (conjgCV k) mulgK -mem_conjg (normalP nH).
have HH: (k * (h * g) * k ^-1) x = z.
   by rewrite 2!permM -Hkx Hkhgx -permM mulgV perm1.
case/negP: diff_hgx_z.
by rewrite -HH !mulgA -h_k_com -!mulgA [k * _]mulgA -g_k_com -!mulgA mulgV mulg1.
Qed.
