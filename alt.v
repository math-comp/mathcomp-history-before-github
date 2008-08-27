Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import div prime tuple finset groups morphisms normal group_perm.
Require Import automorphism action pgroups sylow cyclic signperm.

(* Require Import paths connect finfun zp. *)

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

Lemma trivial_Alt_2 : forall T : finType, #|T| <= 2 -> trivg 'Alt_T.
Proof.
move=> T; rewrite leq_eqVlt; case/predU1P => oT.
  by rewrite trivg_card -[#|_|]half_double -mul2n card_Alt oT.
suffices: (trivg 'Sym_T) by exact: subset_trans (subsetT _).
by rewrite trivg_card card_Sym; case: #|T| oT; do 2?case.
Qed.

Lemma simple_Alt_3 : forall T : finType, #|T| = 3 -> simple 'Alt_T.
Proof.
move=> T T3; have{T3} oA: #|'Alt_T| = 3.
  by apply: double_inj; rewrite -mul2n card_Alt T3.
apply/simpleP; split=> [|K]; [by rewrite trivg_card oA | case/andP=> sKH _].
have:= group_dvdn sKH; rewrite oA dvdn_divisors // !inE orbF orbC /= -oA.
case/orP=> eqK; [right | left]; apply/eqP; rewrite -val_eqE.
  by rewrite eqset_sub_card sKH (eqP eqK) leqnn.
by rewrite eq_sym eqset_sub_card sub1G (eqP eqK) cards1.
Qed.

Lemma not_simple_Alt_4: forall T : finType, #|T| = 4 -> ~~ simple 'Alt_T.
Proof.
move=> T oT; set A := 'Alt_T.
have oA: #|A| = 12 by apply: double_inj; rewrite -mul2n card_Alt oT.
have [p [p_pr pA_int Sp1]]:
  exists p, [/\ prime p, 1 < p_part p #|A| < #|A| & #|gsylow p A| == 1%N].
- pose Syl3 := set_of (gsylow 3 A).
  have: #|Syl3| \in filter [pred d | d %% 3 == 1%N] (divisors 12).
    rewrite mem_filter -dvdn_divisors //= -oA cardsE.
    by rewrite sylow3_div ?sylow3_mod.
  rewrite /= oA; case/orP; first by rewrite cardsE; exists 3; rewrite ?p1_part.
  case/predU1P=> //; move/(congr1 double).
  pose Q3 := \bigcup_(Q \in Syl3) (Q :\ 1).
  have <-: #|Q3| = #|Syl3|.*2.
    rewrite -muln2; apply: card_setnU_id => /= [Q1 Q2 x | Q]; last first.
      rewrite inE /gsylow sylowE oA p1_part; case/andP=> _.
      by rewrite (cardsD1 1) group1; case/eqP.
    rewrite /= !{1}inE /gsylow sylowE; case/andP=> _.
    rewrite oA p1_part -[_ 3 _]/3; move/eqP=> cQ1.
    rewrite sylowE; case/andP=> _.
    rewrite oA p1_part -[_ 3 _]/3; move/eqP=> cQ2.
    case/andP=> nx1 Q1x; rewrite nx1 /= => Q2x.
    apply: val_inj; apply/setP; apply/subset_cardP; first by rewrite cQ1.
    have sQ12: Q1 :&: Q2 \subset Q1 by exact: subsetIl.
    apply/setIidPl; apply/eqP; rewrite eqset_sub_card sQ12 /=.
    have:= group_dvdn sQ12; rewrite cQ1 dvdn_divisors // -topredE /= orbF.
    rewrite {1}(cardD1 1) group1 (cardD1 x) inE [_ x]/= inE nx1 Q1x Q2x /=.
    by move/eqP->.
  move=> /= cQ3; pose Syl2 := gsylow 2 A.
  have{cQ3} nQS2: forall P, P \in Syl2 -> P = A :\: Q3 :> set _.
    move=> P; rewrite /Syl2 /gsylow /in_mem /= sylowE; case/andP=> sAP.
    rewrite oA p1_part -[_ 2 _]/4; move/eqP=> cP.
    apply/setP; apply/subset_cardP.
      apply: (@addn_injl #|A :&: Q3|); rewrite cardsID oA cP addnC; congr _.+4.
      rewrite -[8]cQ3; congr #|(_ : set _)|; apply/setIidPr.
      apply/subsetP=> x; case/bigcupP=> Q; rewrite 2!inE; case/andP=> sAQ _.
      case/andP=> _; exact: (subsetP sAQ).
    apply/subsetP=> x Px; rewrite inE (subsetP sAP) // andbT.
    apply/bigcupP=> [[Q]]; rewrite !inE /gsylow sylowE; case/andP=> _.
    rewrite oA p1_part -[_ 3 _]/3; move/eqP=> cQ; case/andP=> nx1 Qx.
    have sPQP: P :&: Q \subset Q by exact: subsetIr.
    have:= (group_dvdn sPQP); rewrite cQ dvdn_divisors //= !inE orbF.
    rewrite {1}(cardD1 1) (cardD1 x) group1 inE [_ x]/= inE nx1 Px Qx /= -cQ.
    move/eqP=> cPQ; move/(subset_cardP cPQ): sPQP; move/setP; apply/setIidPr.
    by apply/negP; move/group_dvdn; rewrite cP cQ.
  case: ((sylow1_cor [group of A]) 2) => //= P sylP; exists 2.
  rewrite p1_part; split => //.
  rewrite (cardD1 P) [P \in _]sylP eqSS; apply/pred0P=> P'.
  apply/andP=> [[nPP' sylP']]; case/eqP: nPP'.
  by apply: val_inj; rewrite /= !nQS2.
case: (normal_sylowP 'Alt_T p_pr Sp1) => P; rewrite sylowE; case/andP=> sPA sylP nPA.
apply/simpleP=> [] [_]; rewrite -(eqP sylP) in pA_int.
by case/(_ P)=> // defP; rewrite defP oA ?cards1 in pA_int.
Qed.

Module Alt_CP_1. End Alt_CP_1.

Lemma simple_Alt5_base: forall T : finType, #|T| = 5 -> simple 'Alt_T.
Proof.
move=> T oT.
pose tp := is_true_true.
have F1: #|'Alt_T| = 60 by apply: double_inj; rewrite -mul2n card_Alt oT.
have FF: forall H : group _, H <| 'Alt_T -> H <> 1 :> set _ -> 20 %| #|H|.
- move=> H Hh1 Hh3.
  have [x _]: exists x, x \in T by apply/existsP; rewrite /pred0b oT.
  have F2 := Alt_trans T; rewrite oT /= in F2.
  have F3: [transitive ('Alt_T | 'P) on setT] by exact: ntransitive1 F2.
  have F4: [primitive ('Alt_T | 'P) on setT] by exact: ntransitive_primitive F2.
  case: (prim_trans_norm F3 F4 Hh1) => F5.
    case: Hh3; apply/trivgP; exact: subset_trans F5 (aperm_faithful _).
  have F6: 5 %| #|H| by rewrite -oT -cardsT; apply: trans_div (in_setT x) F5. 
  have F7: 4 %| #|H|.
    have F7: #|[set~ x]| = 4 by rewrite cardsC1 oT.
    case: (pickP (mem [set~ x])) => [y Hy | ?]; last by rewrite eq_card0 in F7.
    pose K := 'C_(H | 'P)[x]%G.
    have F8 : K \subset H by apply: subset_astab.
    pose Gx := 'C_('Alt_T | 'P)[x]%G.
    have F9: [transitive * 2 (Gx | 'P) on [set~ x]].
      by rewrite -[[set~ x]]setTI -setD1E stab_ntransitive ?inE.
    have F10: [transitive (Gx | 'P) on [set~ x]].
      exact: ntransitive1 F9.
    have F11: [primitive (Gx | 'P) on [set~ x]].
      exact: ntransitive_primitive F9.
    have F12: K \subset Gx by apply: setSI; exact: normal_sub.
    have F13: K <| Gx by rewrite /(K <| _) F12 norm_stab // normal_norm.
    case: (prim_trans_norm F10 F11 F13) => Ksub; last first.
      apply: dvdn_trans (group_dvdn F8); rewrite -F7; exact: trans_div Hy Ksub.
    have F14: [faithful (Gx | 'P) on [set~ x]].
      apply/subsetP=> g; do 2![case/setIP] => Altg cgx cgx'.
      apply: (subsetP (aperm_faithful 'Alt_T)).
      rewrite inE Altg /=; apply/astabP=> z _.
      case zx': (z \in [set~ x]); first exact: (astabP cgx').
      rewrite inE in zx'; move/eqP: zx' => ->; exact: (astab1P cgx).
    have Hreg: forall g (z : T), g \in H -> g z = z -> g = 1.
      have F15: forall g, g \in H -> g x = x -> g = 1.
        move=> g Hg Hgx; have: g \in K by rewrite inE Hg; apply/astab1P.
        by rewrite (trivGP _ (subset_trans Ksub F14)); move/set1P.
      move=> g z Hg Hgz; have:= in_setT x; rewrite -(atransP F3 z) ?inE //.
      case/imsetP=> g1 Hg1 Hg2; apply: (conjg_inj g1); rewrite conj1g.
      apply: F15; last by rewrite Hg2 -permM mulKVg permM Hgz.
      by case/normalP: Hh1 => _ nH1; rewrite -(nH1 _ Hg1) memJ_conjg.
    clear K F8 F12 F13 Ksub F14.
    case: (Cauchy _ F6) => // h Hh; move/eqP=> Horder.
    have diff_hnx_x: forall n, 0 < n -> n < 5 -> x != (h ^+ n) x.
      move=> n Hn1 Hn2; rewrite eq_sym; apply/negP => HH.
      have: #[h ^+ n] = 5.
        rewrite order_gcd // (eqP Horder).
        by move: Hn1 Hn2 {HH}; do 5 (case: n => [|n] //).
      have Hhd2: h ^+ n \in H by rewrite groupX.
      by rewrite (Hreg _ _ Hhd2 (eqP HH)) order1.
    pose S1 := [tuple x; h x; (h ^+ 3) x].
    have DnS1: S1 \in dtuple_on _ setT.
      rewrite inE memtE subset_all /= !inE /= !negb_or -!andbA /= andbT.
      rewrite -{1}[h]expg1 !diff_hnx_x // expgSr permM.
      by rewrite (inj_eq (@perm_inj _ _)) diff_hnx_x.
    pose S2 := [tuple x; h x; (h ^+ 2) x].
    have DnS2:  S2 \in dtuple_on _ setT.
      rewrite inE memtE subset_all /= !inE /= !negb_or -!andbA /= andbT.
      rewrite -{1}[h]expg1 !diff_hnx_x // expgSr permM.
      by rewrite (inj_eq (@perm_inj _ _)) diff_hnx_x.
    case: (atransP2 F2 DnS1 DnS2) => g Hg [/=].
    rewrite /aperm => Hgx Hghx Hgh3x.
    have h_g_com: h * g = g * h.
      suff HH: (g * h * g^-1) * h^-1 = 1 by rewrite -[h * g]mul1g -HH; gsimpl.
      apply: (Hreg _ x); last first.
        by rewrite !permM -Hgx Hghx -!permM mulKVg mulgV perm1.
      rewrite groupM // ?groupV // (conjgCV g) mulgK -mem_conjg.
      by case/normalP: Hh1 => _ ->.
    have: (g * (h ^+ 2) * g ^-1) x = (h ^+ 3) x.
      rewrite !permM !perm1 -Hgx.
      have ->: h (h x) = (h ^+ 2) x by rewrite /= permM mulg1.
      by rewrite {1}Hgh3x -!permM /= mulgV mulg1 -expgSr.
    rewrite commuteX // mulgK {1}[expgn]lock expgS permM -lock.
    by move/perm_inj=> eqxhx; case/eqP: (diff_hnx_x 1%N tp tp); rewrite expg1.
  by rewrite (@gauss_inv 4 5) // F7.
apply/simpleP; split => [|H Hnorm]; first by rewrite trivg_card F1.
case Hcard1: (#|H| == 1%N); move/eqP: Hcard1 => Hcard1.
  by left; apply/trivGP; rewrite trivg_card Hcard1.
right; case Hcard60: (#|H| == 60%N); move/eqP: Hcard60 => Hcard60.
  apply/eqP; rewrite -val_eqE eqset_sub_card Hcard60 F1 andbT.
  by case/andP: Hnorm.
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
case: (sylow1_cor H prime_5) => S; rewrite sylowE; case/andP=> sSH oS.
have{oS} oS: #|S| = 5 by move/eqP: oS; rewrite p1_part Hcard20. 
suff: 20 %| #|S| by rewrite oS.
apply FF => [|S1]; last by rewrite S1 cards1 in oS.
apply: char_norm_trans Hnorm; apply: lone_subgroup_char => // Q sQH isoQS.
rewrite ((Q =P S :> set _) _) //; apply/idPn=> nQS; move: nSyl5.
rewrite (cardD1 S) (cardD1 Q) -2!topredE {1 2}/gsylow /= nQS sylowE.
by rewrite sSH oS -topredE /= sylowE p1_part Hcard20 sQH (isog_card isoQS) oS.
Qed.

Module Alt_CP_2. End Alt_CP_2.

Section Restrict.

Variable T : finType.
Variable x : T.
Notation T' := {y | y != x}.

Lemma rfd_funP : forall (p : {perm T}) (u : T'),
  let p1 := if p x == x then p else 1 in p1 (val u) != x.
Proof.
move=> p u /=; case: (p x =P x) => [pxx|_]; last by rewrite perm1 (valP u).
apply: contra (valP u); move/eqP=> eq_pux.
by rewrite -(inj_eq (@perm_inj _ p)) eq_pux pxx.
Qed.

Definition rfd_fun p := [fun u => Sub ((_ : perm T) _) (rfd_funP p u) : T'].

Lemma rfdP : forall p, injective (rfd_fun p).
Proof.
move=> p; apply: can_inj (rfd_fun p^-1) _ => u; apply: val_inj => /=.
rewrite -(inj_eq (@perm_inj _ p)) permKV eq_sym.
by case: eqP => _; rewrite !(perm1, permK).
Qed.

Definition rfd p := perm_of (@rfdP p).

Hypothesis card_T : 2 < #|T|.

Lemma rfd_morph : {in 'C_('Sym_T | 'P)[x] &, {morph rfd : y z / y * z}}.
Proof.
move=> p q; rewrite !in_setI !in_setT; move/astab1P=> p_x; move/astab1P=> q_x.
apply/permP=> u; apply: val_inj.
by rewrite permE /= !permM !permE /= [p x]p_x [q x]q_x eqxx permM /=.
Qed.

Canonical Structure rfd_morphism := Morphism rfd_morph.

Definition rgd_fun (p : {perm T'}) :=
  [fun x1 => if insub x1 is Some u then val (p u) else x].

Lemma rgdP : forall p, injective (rgd_fun p).
Proof.
move=> p; apply: can_inj (rgd_fun p^-1) _ => y /=.
case: (insubP _ y) => [u _ val_u|]; first by rewrite valK permK.
by rewrite negbK; move/eqP->; rewrite insubF //= eqxx.
Qed.

Definition rgd p := perm_of (@rgdP p).

Lemma rfd_odd : forall p : {perm T}, p x = x -> rfd p = p :> bool.
Proof.
have rfd1: rfd 1 = 1.
  by apply/permP => u; apply: val_inj; rewrite permE /= if_same !perm1.
have HP0: forall p : {perm T},
  #|[set x | p x != x]| = 0 -> rfd p = p :> bool.
- move => p Hp; suff ->: p = 1 by rewrite rfd1 !odd_perm1.
  apply/permP => z; rewrite perm1.
  suff: z \in [set x | p x != x] = false; first by rewrite inE; move/eqP.
  by rewrite (card0_eq Hp).
move=> p; elim: #|_| {-2}p (leqnn #|[set x | p x != x]|) => {p}[| n Hrec] p Hp Hpx.
  by apply: HP0; move: Hp; case: card.
case Ex: (pred0b (mem [set x | p x != x])); first by apply: HP0; move/eqnP: Ex.
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
rewrite odd_permM odd_tperm eq_sym Hx1 morphM; last 2 first.
- by rewrite 2!inE; exact/astab1P.
- by rewrite 2!inE; apply/astab1P; rewrite -{1}Hpx /= /aperm -permM.
rewrite odd_permM Hrec //=; congr (_ (+) _).
pose x2 : T' := Sub x1 nx1x; pose px2 : T' := Sub (p x1) npx1x.
suff ->: rfd (tperm x1 (p x1)) = tperm x2 px2.
  rewrite odd_tperm; apply/eqP; move/val_eqP => /=.
  by rewrite eq_sym => HH; case/negP: Hx1.
apply/permP => z; apply/val_eqP; rewrite permE /= tpermD // eqxx.
case: (tpermP x2) => [->|->|HH1 HH2]; rewrite /x2 (tpermL, tpermR, tpermD) //.
  by apply/eqP=> HH3; case: HH1; apply: val_inj.
by apply/eqP => HH3; case: HH2; apply: val_inj.
Qed.

Lemma rfd_iso: 'C_('Alt_T | 'P)[x] \isog 'Alt_T'.
Proof.
have rgd_x: forall p, rgd p x = x.
  by move=> p; rewrite permE /= insubF //= eqxx.
have rfd_rgd: forall p, rfd (rgd p) = p.
  move=> p; apply/permP => [[z Hz]]; apply/val_eqP; rewrite !permE.
  rewrite /= [rgd _ _]permE /= insubF eq_refl // permE /=.
  by rewrite (@insubT _ (xpredC1 x) _ _ Hz).
have sSd: 'C_('Alt_T | 'P)[x] \subset 'dom rfd.
  by apply/subsetP=> p; rewrite !inE /=; case/andP.
apply/isogP; exists [morphism of restrm sSd rfd] => /=; last first.
  rewrite morphim_restrm setIid; apply/setP=> z; apply/morphimP/idP=> [[p _]|].
    case/setIP; rewrite Alt_even => Hp; move/astab1P=> Hp1 ->.
    by rewrite Alt_even /even_perm rfd_odd.
  have dz': rgd z x == x by rewrite rgd_x.
  move=> kz; exists (rgd z); last by rewrite /= rfd_rgd.
    by rewrite 2!inE (sameP astab1P eqP).
  rewrite 4!inE /= (sameP astab1P eqP) dz' -rfd_odd; last exact/eqP.
  by rewrite rfd_rgd mker // ?set11.
apply/injmP=> x1 y1 /=.
case/setIP=> Hax1; move/astab1P; rewrite /= /aperm => Hx1.
case/setIP=> Hay1; move/astab1P; rewrite /= /aperm => Hy1 Hr.
apply/permP => z.
case (z =P x) => [->|]; [by rewrite Hx1 | move/eqP => nzx].
move: (congr1 (fun q : {perm T'} => q (Sub z nzx)) Hr).
by rewrite !permE; move/val_eqP; rewrite /= Hx1 Hy1 !eqxx; move/eqP.
Qed.

End Restrict.

Module Alt_CP_3. End Alt_CP_3.

Lemma simple_Alt5 : forall T : finType, #|T| >= 5 -> simple 'Alt_T.
Proof.
pose tp := is_true_true.
suff F1: forall n (T : finType), #|T| = n + 5 -> simple 'Alt_T.
  move=> T H; apply: (F1 (#|T| - 5)).
  by rewrite addnC subnK.
elim => [| n Hrec T Hde]; first exact: simple_Alt5_base.
have oT: 5 < #|T| by rewrite Hde addnC.
apply/simpleP; split=> [|H Hnorm]; last have [Hh1 nH] := andP Hnorm. 
  rewrite trivg_card -[#|_|]half_double -mul2n card_Alt Hde addnC //.
  by rewrite addSn /fact -/fact mulnC -(prednK (ltn_0fact _)).
case E1: (pred0b T); first by rewrite /pred0b in E1; rewrite (eqP E1) in oT.
case/pred0Pn: E1 => x _; have Hx := in_setT x.
have F2: [transitive * 4 ('Alt_T | 'P) on setT].
  by apply: ntransitive_weak (Alt_trans T); rewrite -(subnK oT).
have F3 := ntransitive1 (tp: 0 < 4) F2.
have F4 := ntransitive_primitive (tp: 1 < 4) F2.
case Hcard1: (#|H| == 1%N); move/eqP: Hcard1 => Hcard1.
  by left; apply/trivGP; rewrite trivg_card Hcard1.
right; case: (prim_trans_norm F3 F4 Hnorm) => F5.
  by rewrite (trivGP H (subset_trans F5 (aperm_faithful _))) cards1 in Hcard1.
case E1: (pred0b (predD1 T x)).
  rewrite /pred0b in E1; move: oT.
  by rewrite (cardD1 x) (eqP E1); case: (T x).
case/pred0Pn: E1 => y Hdy; case/andP: (Hdy) => diff_x_y Hy.
pose K := 'C_(H | 'P)[x]%G.
have F8: K \subset H by apply: subset_astab.
pose Gx := 'C_('Alt_T | 'P)[x]%G.
have F9: [transitive * 3 (Gx | 'P) on [set~ x]].
  by rewrite -[[set~ x]]setTI -setD1E stab_ntransitive ?inE.
have F10: [transitive (Gx | 'P) on [set~ x]].
  by apply: ntransitive1 F9.
have F11: [primitive (Gx | 'P) on [set~ x]].
  by apply: ntransitive_primitive F9.
have F12: K \subset Gx by rewrite setSI // normal_sub.
have F13: K <| Gx by apply/andP; split; last apply: norm_stab.
have:= prim_trans_norm F10 F11; case/(_ K) => //= => Ksub; last first.
  have F14 := (subgroup_transitive Hx Hh1 F3 F5); rewrite -/Gx /= in F14.
  have: simple Gx.
    apply: isog_simpl (isog_sym_imply (rfd_iso x)) (Hrec _ _) => /=.
    by rewrite card_sub cardC1 Hde.
  case/simpleP=> _; case/(_ [group of K] F13) => /= [] [HH2].
    case Ez: (pred0b (predD1 (predD1 T x) y)).
      move: oT; rewrite /pred0b in Ez.
      by rewrite (cardD1 x) (cardD1 y) (eqP Ez) inE /= inE /= diff_x_y.  
    case/pred0Pn: Ez => z; case/andP => diff_y_z Hdz; case/andP: (Hdz) => diff_x_z Hz.
    have: z \in [set~ x] by rewrite inE.
    rewrite -(atransP Ksub y) ?inE //; case/imsetP => g.
    rewrite /= HH2 inE; move/eqP => -> HH4.
    by case/negP: diff_y_z; rewrite HH4 act1.
  by apply: val_inj; rewrite /= -F14 -HH2 (mulSGid F8).
have F14: [faithful (Gx | 'P) on [set~ x]].
  apply: subset_trans (aperm_faithful 'Sym_T); rewrite subsetI subsetT.
  apply/subsetP=> g; do 2![case/setIP]=> _ cgx cgx'; apply/astabP=> z _ /=.
  case zx': (z \in [set~ x]); first exact: (astabP cgx').
  rewrite inE in zx'; move/eqP: zx' ->; exact: (astab1P cgx).
have Hreg: forall g z, g \in H -> g z = z -> g = 1.
  have F15: forall g, g \in H -> g x = x -> g = 1.
    move=> g Hg Hgx; have: g \in K by rewrite inE Hg; apply/astab1P.
    by rewrite [K](trivGP _ (subset_trans Ksub F14)); move/set1P.
  move=> g z Hg Hgz; have:= in_setT x; rewrite -(atransP F3 z) ?inE //.
  case/imsetP=> g1 Hg1 Hg2; apply: (conjg_inj g1); rewrite conj1g.
  apply: F15; last by rewrite Hg2 -permM mulKVg permM Hgz.
  by rewrite memJ_norm ?(subsetP nH).
clear K F8 F12 F13 Ksub F14.
have Hcard: 5 < #|H|.
  apply: (leq_trans oT); apply dvdn_leq; first by exact: pos_card_group.
  by rewrite -cardsT (trans_div Hx F5).
case Eh: (pred0b [predD1 H & 1]).
  by move: Hcard; rewrite /pred0b in Eh; rewrite (cardD1 1) group1 (eqP Eh).
case/pred0Pn: Eh => h; case/andP => diff_1_h /= Hh.
case Eg: (pred0b (predD1 (predD1 [predD1 H & 1] h) h^-1)).
  move: Hcard; rewrite ltnNge; case/negP.
  rewrite (cardD1 1) group1 (cardD1 h) (cardD1 h^-1) (eqnP Eg).
  by do 2!case: (_ \in _).
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
  by apply: (Hreg _ x); [exact: groupM | apply/eqP].
case diff_hgx_hx: ((h * g) x == h x).
  case/negP: diff_1_g; apply/eqP.
  by apply: (Hreg _ (h x)) => //; apply/eqP; rewrite -permM.
case diff_hgx_gx: ((h * g) x == g x).
  case/eqP: diff_hx_x; apply: (@perm_inj _ g) => //.
  by apply/eqP; rewrite -permM.
case Ez: (pred0b
            (predD1 (predD1 (predD1 (predD1 T x) (h x)) (g x)) ((h * g) x))).
- move: oT; rewrite /pred0b in Ez.
  rewrite (cardD1 x) (cardD1 (h x)) (cardD1 (g x)) (cardD1 ((h * g) x)).
  by rewrite (eqP Ez); do 3!case: (_ x \in _).
case/pred0Pn: Ez => z.
case/and5P=> diff_hgx_z diff_gx_z diff_hx_z diff_x_z /= Hz.
pose S1 := [tuple x; h x; g x; z].
have DnS1: S1 \in dtuple_on 4 setT.
  rewrite inE memtE subset_all -!andbA !negb_or /= !inE !andbT.
  rewrite -!(eq_sym z) diff_gx_z diff_x_z diff_hx_z.
  by rewrite !(eq_sym x) diff_hx_x diff_gx_x eq_sym diff_gx_hx.
pose S2 := [tuple x; h x; g x; (h * g) x].
have DnS2: S2 \in dtuple_on 4 setT.
  rewrite inE memtE subset_all -!andbA !negb_or /= !inE !andbT !(eq_sym x).
  rewrite diff_hx_x diff_gx_x diff_hgx_x.
  by rewrite !(eq_sym (h x)) diff_gx_hx diff_hgx_hx eq_sym diff_hgx_gx.
case: (atransP2 F2 DnS1 DnS2) => k Hk [/=].
rewrite /aperm => Hkx Hkhx Hkgx Hkhgx.
have h_k_com: h * k = k * h.
  suff HH: (k * h * k^-1) * h^-1 = 1 by rewrite -[h * k]mul1g -HH; gsimpl.
  apply: (Hreg _ x); last first.
    by rewrite !permM -Hkx Hkhx -!permM mulKVg mulgV perm1.
  by rewrite groupM // ?groupV // (conjgCV k) mulgK -mem_conjg (normsP nH).
have g_k_com: g * k = k * g.
  suff HH: (k * g * k^-1) * g^-1 = 1 by rewrite -[g * k]mul1g -HH; gsimpl.
  apply: (Hreg _ x); last first.
    by rewrite !permM -Hkx Hkgx -!permM mulKVg mulgV perm1.
  by rewrite groupM // ?groupV // (conjgCV k) mulgK -mem_conjg (normsP nH).
have HH: (k * (h * g) * k ^-1) x = z.
   by rewrite 2!permM -Hkx Hkhgx -permM mulgV perm1.
case/negP: diff_hgx_z.
by rewrite -HH !mulgA -h_k_com -!mulgA [k * _]mulgA -g_k_com -!mulgA mulgV mulg1.
Qed.
