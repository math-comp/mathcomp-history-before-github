Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp action.
Require Import normal sylow cyclic signperm.

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

Section Alt.

Variable d : finType.

Notation Local oddp := (@odd_perm d).

Definition sym := Group (group_set_finGroupType (perm_finGroupType d)).

Lemma dom_odd_perm : dom oddp = perm_finGroupType d.
Proof.
apply/isetP; apply/subset_eqP; apply/andP; split; apply/subsetP=> x //.
move=> _; case Ix : (odd_perm x);  [rewrite dom_nu // | rewrite dom_k //].
  by rewrite Ix.
apply/kerP=> y; move: Ix; rewrite odd_permM.
by case: odd_perm.
Qed.

Lemma group_set_dom_odd_perm : group_set (dom oddp).
Proof.
by rewrite dom_odd_perm; apply/andP; split => //; apply/subsetP=> u.
Qed.

Definition sign_morph: morphism (perm_finGroupType d) boolGroup.
exists oddp; first exact: group_set_dom_odd_perm.
move => *; exact: odd_permM.
Defined.

Definition alt :=  Group (group_set_ker sign_morph).

Lemma altP: forall x, reflect (even_perm x) (alt x).
Proof.
move=> x; apply: (iffP idP); rewrite /even_perm => H1; first by move: (mker H1) => /= ->.
by apply/kerP => /= y; move: H1; rewrite odd_permM; case: odd_perm.
Qed.

Lemma alt_subset: subset alt sym.
Proof.
Set Printing All.

by apply/subsetP => x; rewrite !s2f.
Qed.

Lemma alt_normal: alt <| sym.
Proof.
by rewrite /isetA /= -dom_odd_perm; exact: (normal_ker sign_morph).
Qed.

Lemma alt_index: 1 < card (setA d) -> indexg alt sym = 2.
Proof.
move=> H.
have F1: ker_(sym) oddp = alt.
  apply/isetP => z; apply/idP/idP; rewrite /isetI /= s2f; first by case/andP.
  by move => -> /=; rewrite s2f.
rewrite -card_quotient ?alt_normal // -F1.
have F: isog (sym/ ker_(sym) oddp) (oddp @: sym).
  have F2: subset sym (dom oddp) by rewrite dom_odd_perm; apply/subsetP.
  exact: (@first_isom _ _ sign_morph _ F2).
case: F => g; case/andP => H1; move/injmP => /= H2.
rewrite /= in H1.
rewrite -(card_diimage H2) (eqP H1).
have <-: card boolGroup = 2 by rewrite eq_cardA // => x; rewrite s2f.
apply eq_card => z; apply/idP/idP; first by rewrite s2f.
case: z => _; last first.
  apply/iimageP; exists (1:perm_finGroupType d) => //.
  by rewrite odd_perm1.
case: (pickP (setA d)) => [x1 Hx1 | HH]; move: H; last first.
  by rewrite (eq_card HH) card0.
rewrite (cardD1 x1) Hx1.
case: (pickP (setD1 (setA d) x1)) => [x2 Hx2 | HH1]; last by rewrite (eq_card HH1) card0.
case/andP: Hx2 => Hx2 Hy2 _; apply/iimageP; exists (transperm x1 x2) => //.
by rewrite odd_transp.
Qed.

Let n := card (setA d).

Lemma card_sym: card sym = fact (card (setA d)).
Proof.
by rewrite - (card_perm (setA d)); apply:eq_card =>  z; rewrite s2f; apply sym_equal;apply/subsetP. 
Qed.

Lemma card_alt0: card (setA d) <= 1 -> card alt = 1%N.
move=> Hcard; have cardS: card sym = 1%N.
  by rewrite card_sym; move: Hcard; case: card => // n1; case: n1.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  by rewrite -cardS subset_leq_card // alt_subset.
by rewrite (cardD1 1) group1.
Qed.

Lemma card_alt: 1 < card (setA d) -> card alt = divn (fact n) 2.
Proof.
move=> Hcard; suff ->: (fact n = 2 * card alt)%N by rewrite divn_mulr.
by rewrite -card_sym -alt_index 1?mulnC ?LaGrange ?alt_subset.
Qed.

Let gt1: tuple.tuple_finType d n.
by exists (enum d); rewrite card_ordinal.
Defined.

Definition dsym1: dtuple d n.
by exists gt1; rewrite /gt1 /distinctb; exact: uniq_enum.
Defined.

Let d2p_aux:
 forall (t: seq d),
 size t = card (setA I_(n)) ->  size t = card (setA d).
Proof.
by move=> t; rewrite card_ordinal.
Qed.

Definition d2p: dtuple d n -> (permType d).
by move=> [[t Hs] Ht]; apply Perm; exists (Fgraph (d2p_aux Hs)).
Defined.

Lemma d2p_sym: forall t, sym (d2p t).
Proof.
by move=> [[t Ht] Dt]; rewrite s2f.
Qed.

Lemma eq_maps_s : forall (d1 d2: eqType) (f1 f2 : d1 -> d2) (l: seq d1), 
  (forall x, l x ->  f1 x = f2 x) -> maps f1 l = maps f2 l.
Proof.
move=> d1 d2 f1 f2; elim => [|a l Hrec] H //=.
rewrite (H a) // ?Hrec //= /setU1 ?eq_refl //.
by move=> x H1; rewrite H //= /setU1 H1 orbT.
Qed.

Lemma eq_maps_same : forall (d1: eqType) (l1 l2: seq d1)
                             (f: d1 -> d1),
  size l1 = size l2 -> uniq l2 ->
  maps (fun z => sub (f z) l1 (index z l2)) l2 = l1.
Proof.
move=> d1; elim => [| b l1 Hrec] [|c l2] //.
move=> f Hs; case/andP => Hc Hf; rewrite /= eq_refl.
congr Adds; rewrite -{2}(Hrec l2 f) //; last by case: Hs.
apply: eq_maps_s => e He; case Ec: (e == c) => //.
by case/negP: Hc; rewrite -(eqP Ec).
Qed.

Lemma d2p_sym1: forall t,
   naction (perm_act d) n dsym1 (d2p t) = t.
Proof.
move=> [[t Ht] Dt]; apply/val_eqP.
rewrite /set1 /= /to  /fun_of_perm /fun_of_fgraph; unlock.
apply/eqP; apply: eq_maps_same; last by exact: uniq_enum.
by rewrite Ht card_ordinal.
Qed.

Lemma sym_trans: ntransitive (perm_act d) sym (setA d) n.
Proof.
split; last by exact: max_card.
move=> x Hx y; apply/iimageP/idP => [[z Hz Hz1] | H1].
  by exact: dliftA.
exists ((d2p x)^-1 * (d2p y)); first by rewrite s2f.
rewrite act_morph -{1}(d2p_sym1 x) -!act_morph; gsimpl.
by rewrite (d2p_sym1 y).
Qed.

Lemma alt_trans: ntransitive (perm_act d) alt (setA d) (n - 2).
Proof.
case (leqP n 2); first by rewrite -eqn_sub0; move/eqP => ->; exact: ntransitive0.
move => Hn.
have Hn1: 1 < n by apply: leq_trans Hn.
have Hn2: n = n - 2 + 1 + 1. by rewrite -addnA addnC leq_add_sub.
have Hn3: 0 < n - 2 + 1 + 1 by rewrite -Hn2; apply: leq_trans Hn1.
have Hn4: 0 < n - 2 + 1 by rewrite addnC ltnS leq_eqVlt ltn_0sub Hn orbT.
split; last by rewrite -/n leq_subr.
move => x Hx y; apply/iimageP/idP => [[z Hz ->] | H1]; first by exact: dliftA.
have F: card(setC (dtuple_get x)) == 2.
  by rewrite -(eqn_addr (n - 2)) leq_add_sub //
          -{2}(dtuple_get_card x) addnC cardC.
case: (pickP (setC (dtuple_get x))) => 
        [a1 Ha1 | HH]; last by move: F; rewrite (eq_card HH) card0.
case: (pickP (setD1 (setC (dtuple_get x)) a1)) => 
        [a2 {F}Ha2 | HH]; last by move: F; rewrite (cardD1 a1) (eq_card HH) Ha1 card0.
have F: card(setC (dtuple_get y)) == 2.
  by rewrite -(eqn_addr (n - 2)) leq_add_sub //
          -{2}(dtuple_get_card y) addnC cardC.
case: (pickP (setC (dtuple_get y))) => 
        [b1 Hb1 | HH]; last by move: F; rewrite (eq_card HH) card0.
case: (pickP (setD1 (setC (dtuple_get y)) b1)) => 
        [b2 {F}Hb2 | HH]; last by move: F; rewrite (cardD1 b1) (eq_card HH) Hb1 card0.
pose x1 := dtuple_add Ha1; have Fx1: ~~ dtuple_in a2 x1.
  rewrite /x1 /dtuple_in; case: (x) (Ha1) (Ha2); case => /= v _ _ _.
  by case/andP => HH1 HH2; apply/norP; split.
pose y1 := dtuple_add Hb1; have Fy1: ~~ dtuple_in b2 y1.
  rewrite /y1 /dtuple_in /distinctb.
  case: (y) (Hb1) (Hb2); case => /= v _ _ _.
  by case/andP => HH1 HH2; apply/norP; split.
pose x2 := dtuple_add Fx1; pose y2 := dtuple_add Fy1.
move: sym_trans; rewrite {1}Hn2; case => FF _.
move: (dliftA y2); rewrite -(@FF _ (dliftA x2)).
case/iimageP => g Hg Hg1.
case Pm: (odd_perm g); last first.
  exists g; first by apply/kerP => h; rewrite /= odd_permM Pm.
  have ->: x = (dtuple_tl (dtuple_tl x2)) by rewrite !dtuple_tl_add.
  by rewrite -!naction_tl -Hg1 !dtuple_tl_add.
pose (g1:= transperm b1 b2); exists (g * g1) => [/= |].
  apply/kerP => h; rewrite !odd_permM Pm odd_transp.
  by case/andP: (Hb2) => ->.
have ->: x = (dtuple_tl (dtuple_tl x2)) by rewrite !dtuple_tl_add.
rewrite act_morph -!naction_tl -Hg1.
have Fy3: ~~ dtuple_in b2 y.
  rewrite /dtuple_in /distinctb; case: (y) (Hb1) (Hb2); case => /= v _ _ _.
  by case/andP.
pose y3 := dtuple_add Fy3; have Fy4: ~~ dtuple_in b1 y3.
  rewrite /y3 /dtuple_in /distinctb /=.
  case: (y) (Fy3) (Hb1) (Hb2) => [[v]] /= _ _ _ HH.
  by case/andP => HH1 HH2; apply/norP; split; rewrite // eq_sym.
pose y4 := dtuple_add Fy4.
suff ->: naction (perm_act d) (n -2 + 1 + 1) y2 g1 = y4 by rewrite !dtuple_tl_add.
apply: (dtuple_hd_tl (x:= a1)).
  rewrite dtuple_hd_add naction_hd /= /to /g1 // dtuple_hd_add.
  by case: (transpP b1 b2 b2).
rewrite dtuple_tl_add naction_tl dtuple_tl_add.
apply: (dtuple_hd_tl (x:= a1)).
  rewrite dtuple_hd_add naction_hd /= /to /g1 // dtuple_hd_add.
  by case: (transpP b1 b2 b1).
rewrite dtuple_tl_add naction_tl dtuple_tl_add.
case: (y) (Hb1) (Fy3); case.
rewrite /dtuple_in /distinctb /setC /= => z Hz Hz0 Hz1 Hz2.
apply/val_eqP; rewrite /set1 /=; apply/eqP.
elim: (z) Hz1 Hz2 =>  [|a z1 Hrec] //=.
case/norP => Hz3 Hz4; case/norP => Hz5 Hz6.
congr Adds; last by exact: Hrec.
by rewrite /to /g1; case: (transpP b1 b2 a) Hz3 Hz5 => // ->; rewrite eq_refl.
Qed.

Lemma perm_act_faithful: faithful (perm_act d) alt (setA d).
Proof.
apply/faithfulP => x H.
apply /eqP; apply/ perm_act1P.
by move=> y; move: (H y); case.
Qed.

End Alt.

Lemma simple_alt_1: forall d: finType, card (setA d) <= 3 -> simple (alt d).
Proof.
move=> d; rewrite leq_eqVlt; case/orP => Hcard; last first.
  have F1: card (alt d) = 1%N by
    (rewrite ltnS leq_eqVlt in Hcard; case/orP: Hcard => Hcard); 
     [rewrite card_alt (eqP Hcard) | rewrite card_alt0].
  apply/simpleP => K Hs Hn; left; apply/subset_eqP.
  apply/andP; split; apply/subsetP => x; last first.
  move/eqP => <-; exact: group1.
  move=> Kx; move: (subset_leq_card Hs).
  by rewrite F1 (cardD1 1) group1 (cardD1 x) /setD1 Kx; case: (_ == _).
have F1: card (alt d) = 3%N by rewrite card_alt (eqP Hcard).
apply/simpleP => K Hs Hn.
case E0: (set0b (setD1 K 1)).
  left; apply fsym; apply/subset_cardP.
    by rewrite /set0b in E0; rewrite card1 (cardD1 1) group1 -(eqP E0).
  by apply/subsetP => z Hz; rewrite -(eqP Hz) group1.
case/set0Pn: E0=> x; case/andP => diff_1_x Kx.
have alt_x: alt d x by rewrite (subsetP Hs).
case Ey: (set0b (setD1 (setD1 (alt d) 1) x)).
  rewrite/set0b in Ey; move: F1.
  by rewrite (cardD1 1) group1 (cardD1 x) (eqP Ey) /setD1 diff_1_x alt_x.
case/set0Pn: Ey => y ; case/andP => diff_x_y; case/andP=> diff_1_y alt_y.
have alt_xy: alt d (x * y) by apply: groupM.
move: (F1); rewrite (cardD1 1) (cardD1 x) (cardD1 y) (cardD1 (x * y)) /setD1
                  group1 alt_x alt_y alt_xy diff_1_x diff_1_y !diff_x_y.
case E0: (y == x * y).
  case/negP: diff_1_x; have ->: x = (x * y) * y^-1 by gsimpl.
  by rewrite -(eqP E0) mulgV.
case E1: (x == x * y).
  case/negP: diff_1_y; have ->: y = x^-1 * (x * y) by gsimpl.
  by rewrite -(eqP E1)  mulVg.
case E2: (1 == x * y) => //.
have Ky: K y.
  have ->: y = x^-1 * (x * y) by gsimpl.
  by rewrite groupM ?groupV // -(eqP E2) group1.
right; apply/subset_cardP => //.
apply/eqP; rewrite eqn_leq (subset_leq_card Hs) F1.
by rewrite (cardD1 1) (cardD1 x) (cardD1 y) /setD1 group1 Kx Ky diff_1_x diff_x_y diff_1_y.
Qed.

(* Simplication of trans p *)
Ltac transp_tac_aux t := match t with
  fun_of_perm _  (fun_of_perm ?X ?Y) => 
     let z := constr: (fun_of_perm X Y) in (transp_tac_aux z) 
| fun_of_perm (transperm ?X ?Y) ?Z => 
        (rewrite (@transpD _ X Y Z) //; try (rewrite eq_sym; done))
end.

Ltac transp_tac :=
  rewrite transpR || rewrite transpL ||
  match goal with |- context [fun_of_perm ?X ?Y] =>
     let z := constr: (fun_of_perm X Y) in (transp_tac_aux z)
  end.

(* use of injectivity of permutation to remove impossible case *)
Ltac iperm_tac := match goal with 
H: ?X = fun_of_perm ?U ?Y,
H1: ?X = fun_of_perm ?U ?Z |- _ => rewrite H in H1;
match goal with 
D: is_true (negb (set1 Y Z)) |- _ => 
 by case/negP: D; apply/eqP; apply: (@inj_act _ _ (perm_act _) U)
| D: is_true (negb (set1 Z Y)) |- _ => 
 by case/negP: D; apply/eqP; apply: (@inj_act _ _ (perm_act _) U)
end
end.

Lemma not_simple_alt_4: forall d: finType, card (setA d) = 4 -> ~ (simple (alt d)).
Proof.
move => d card_d.
(* We exhibit the element of d. *)
case Ex1: (set0b (setA d)).
  by move: card_d; rewrite /set0b in Ex1; rewrite (eqP Ex1).
case/set0Pn: Ex1 => x1 d_x1.
case Ex2: (set0b (setD1 (setA d) x1)).
  by move: card_d; rewrite /set0b in Ex2; rewrite (cardD1 x1) d_x1 (eqP Ex2).
case/set0Pn: Ex2 => x2; case/andP => diff_x1_x2 d_x2.
case Ex3: (set0b (setD1 (setD1 (setA d) x1) x2)).
  move: card_d; rewrite /set0b in Ex3; 
  by rewrite (cardD1 x1) (cardD1 x2) /setD1 d_x1 d_x2 diff_x1_x2 (eqP Ex3).
case/set0Pn: Ex3 => x3; case/andP => diff_x2_x3; case/andP => diff_x1_x3 d_x3.
case Ex4: (set0b (setD1 (setD1 (setD1 (setA d) x1) x2) x3)).
  move: card_d; rewrite /set0b in Ex4; 
  by rewrite (cardD1 x1) (cardD1 x2) (cardD1 x3) /setD1 
             d_x1 d_x2 d_x3 diff_x1_x2 diff_x1_x3 diff_x2_x3 (eqP Ex4).
case/set0Pn: Ex4 => x4; case/andP => diff_x3_x4; case/andP => diff_x2_x4;
                        case/andP => diff_x1_x4 d_x4.
have d_inv: forall z, [|| x1 == z, x2 == z, x3 == z | x4 == z].
  move => z; move: card_d.
  rewrite (cardD1 x1) (cardD1 x2) (cardD1 x3) (cardD1 x4) (cardD1 z) /setD1
          diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4
          d_x1 d_x2 d_x3 d_x4 /setA.
  by do 4 (case: (_ == _) => //).
(* Here are the elements of the normal subgroup *)
pose el1 := (transp x1 x2) * (transp x3 x4).
pose el2 := (transp x1 x3) * (transp x2 x4).
pose el3 := (transp x1 x4) * (transp x2 x3).
pose S := {: 1} :|: {: el1} :|: {: el2}:|: {: el3}.
have Sel1: S el1 by rewrite /S !s2f eq_refl !orbT.
have Sel2: S el2 by rewrite /S !s2f eq_refl !orbT.
have Sel3: S el3 by rewrite /S !s2f eq_refl !orbT.
(* It is a group *)
have group_S: group_set S.
  (* Multiplication table *)
  have el12: el1 * el1 = 1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM perm1;
      repeat transp_tac.
  have el22: el2 * el2 = 1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM perm1;
      repeat transp_tac.
  have el32: el3 * el3 = 1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM perm1;
      repeat transp_tac.
  have el1_el2: el1 * el2 = el3.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el2_el1: el2 * el1 = el3.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el1_el3: el1 * el3 = el2.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el3_el1: el3 * el1 = el2.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el2_el3: el2 * el3 = el1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  have el3_el2: el3 * el2 = el1.
    apply: eq_fun_of_perm => z.
    by case/or4P: (d_inv z); move/eqP => <-; rewrite /el1 /el2 /el3 !permM;
      repeat transp_tac.
  rewrite /group_set {1}/S.
  rewrite /isetU !s2f eq_refl; apply/subsetP => x.
  case/smulgP => elx ely Sx Sy ->.
  move: Sx Sy; rewrite {1}/S /isetU !s2f.
  rewrite -!orb_assoc; case/or4P => E0; rewrite -{E0}(eqP E0) ?mul1g //;
    case/or4P => E0; rewrite -{E0}(eqP E0) ?mulg1 ?el12 ?el22 ?el32
     ?el1_el2 ?el2_el1 ?el1_el3 ?el3_el1 ?el2_el3 ?el3_el2 ?eq_refl ?orbT //.
(* It is a subset of alt *)
have S_subset: subset S (alt d).
  apply/subsetP => x.
  rewrite {1}/S /isetU 7!s2f -!orb_assoc; case/or4P => E0; 
     rewrite -{E0}(eqP E0) ?group1 //; apply/altP;
     rewrite /even_perm odd_permM !odd_transp 
             ?diff_x1_x2 ?diff_x1_x3 ?diff_x1_x4 ?diff_x2_x3 
             ?diff_x2_x4 ?diff_x3_x4 //.
(* It is normal *)
have S_norm: S <| alt d.
  have Sel1t: S (transp x3 x4 * transp x1 x2).
    suff <-: el1 = transp x3 x4 * transp x1 x2 by done.
    apply/eqP; apply: transpCom.
    move: diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4.
    rewrite /= /setU1 ?(eq_sym x2 x1) ?(eq_sym x3 x1)?(eq_sym x4 x1)
           ?(eq_sym x3 x2)  ?(eq_sym x4 x2) ?(eq_sym x4 x3);
    do 6 (case: (_ == _) => //).
  have Sel2t: S (transp x2 x4 * transp x1 x3).
    suff <-: el2 = transp x2 x4 * transp x1 x3 by done.
    apply/eqP; apply: transpCom.
    move: diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4.
    rewrite /= /setU1 ?(eq_sym x2 x1) ?(eq_sym x3 x1)?(eq_sym x4 x1)
         ?(eq_sym x3 x2)  ?(eq_sym x4 x2) ?(eq_sym x4 x3);
    do 6 (case: (_ == _) => //).
  have Sel3t: S (transp x2 x3 * transp x1 x4).
    suff <-: el3 = transp x2 x3 * transp x1 x4 by done.
    apply/eqP; apply: transpCom.
    move: diff_x1_x2 diff_x1_x3 diff_x1_x4 diff_x2_x3 diff_x2_x4 diff_x3_x4.
    rewrite /= /setU1 ?(eq_sym x2 x1) ?(eq_sym x3 x1)?(eq_sym x4 x1)
         ?(eq_sym x3 x2)  ?(eq_sym x4 x2) ?(eq_sym x4 x3);
    do 6 (case: (_ == _) => //).
  apply/normalP => x Hx; apply norm_sconjg.
  rewrite /normaliser /= s2f; apply/subsetP =>y.
  rewrite /sconjg s2f.
  by rewrite {1}/S /isetU 7!s2f -!orb_assoc; case/or4P => E0;
  move: (conjgKv x y); rewrite /cancel => <-; rewrite -(eqP E0) {E0};
  first (by rewrite conj1g /S !s2f eq_refl);
   rewrite /el1 /el2 /el3 conjg_mul !transpJ;
    case/or4P: (d_inv (x x1)); move/eqP => Ex1; rewrite -Ex1;
    case/or4P: (d_inv (x x2)); move/eqP => Ex2; rewrite -Ex2; try iperm_tac;
    case/or4P: (d_inv (x x3)); move/eqP => Ex3; rewrite -Ex3; (try iperm_tac);
    case/or4P: (d_inv (x x4)); move/eqP => Ex4; rewrite -Ex4; (try iperm_tac);
     rewrite ?(transpC x4) ?(transpC x2 x1) ?(transpC x3 x2) ?(transpC x3 x1)
             ?(transpC x4 x3) -/el1 -/el2 -/el3.
move /simpleP ; case /(_ (Group group_S) S_subset S_norm) => /= HH.
  case/negP: diff_x1_x2; apply/eqP.
  have: el1 x1 = x2  by rewrite /el1 permM; repeat transp_tac.
  by move: Sel1; rewrite HH; move/eqP => <-; rewrite perm1 => HH1.
pose el4:= transp x1 x2 * transp x2 x3.
have: alt d el4.
  apply/altP; rewrite /even_perm odd_permM !odd_transp.
  by rewrite diff_x1_x2 diff_x2_x3.
rewrite -HH /S.
have el4_1: el4 x1 = x3  by rewrite /el4 permM; repeat transp_tac.
have el4_2: el4 x2 = x1 by rewrite /el4 permM; repeat transp_tac.
have el4_3: el4 x3 = x2 by rewrite /el4 permM; repeat transp_tac.
rewrite !s2f -!orbA; case/or4P.
- by move/eqP => HH1; case/negP: diff_x1_x3; rewrite -el4_1 -HH1 perm1.
- move/eqP => HH1; case/negP: (diff_x2_x3); rewrite -el4_1 -HH1.
  by rewrite /el1 permM; repeat transp_tac.
- move/eqP => HH1; case/negP: (diff_x1_x4); rewrite -el4_2 -HH1.
  by rewrite /el2 permM; repeat transp_tac.
move/eqP => HH1; case/negP: (diff_x3_x4); rewrite -el4_1 -HH1.
by rewrite /el3 permM; repeat transp_tac.
Qed.

(* trivial proof *)
Let tp := refl_equal true.

Let simple_alt5_base: forall d: finType, card (setA d) = 5 -> simple (alt d).
Proof.
move => d Hd.
have F1: card (alt d) = 60.
  by rewrite -[60]/(divn (fact 5) 2) -Hd -card_alt ?divn_mulr // Hd.
have FF: forall H: group _, subset H (alt d) -> H <| alt d -> ~ H =1 set1 1 -> 
                   dvdn 20 (card H).
  move=> H Hh1 Hh2 Hh3.
  case E1: (set0b (setA d)); first by rewrite /set0b Hd in E1.
  case/set0Pn: E1 => x Hx.
  have F2 := alt_trans d; rewrite Hd in F2.
  have F3 := ntransitive1 (tp: 0 < 3) F2.
  have F4 := ntransitive_primitive (tp: 1 < 3) F2.
  case: (prim_trans_norm F3 F4 Hh1 Hh2) => F5.
    case: Hh3; move => z; apply/idP/eqP => Hz; last by rewrite -Hz group1.
    apply/eqP; move: (perm_act_faithful d); rewrite /faithful.
    rewrite (cardD1 1) (cardD1 z) akernel1 /setD1.
    case: (1 == _); case E1: (akernel _ _ _ z) => //.
    by case/idP: E1; apply: (subsetP F5).
  have F6: dvdn 5 (card H) by rewrite -Hd; apply: (trans_div Hx F5). 
  have F7: dvdn 4 (card H).
    have F7: card (setD1 (setA d) x) = 4.
      apply/eqP; rewrite -(eqn_addl 1) /=; apply/eqP.
      by move: Hd; rewrite (cardD1 x) Hx.
    case E1: (set0b (setD1 (setA d) x)); first by rewrite /set0b F7 in E1.
    case/set0Pn: E1 => y Hy.
    pose K := group_stab (perm_act d) H x.
    have F8: subset K H by apply: subset_stab.
    pose Gx := group_stab (perm_act d) (alt d) x.
    have F9: ntransitive (perm_act d) Gx (setD1 (setA d) x) (3 - 1) by apply:  stab_ntransitive.
    have F10: transitive (perm_act d) Gx (setD1 (setA d) x) by apply:  ntransitive1 F9.
    have F11: primitive (perm_act d) Gx (setD1 (setA d) x) by apply: ntransitive_primitive F9.
    have F12: subset K Gx.
      apply/subsetP=> g; case/stabiliserP => Hg Hperm.
      by apply/stabiliserP; split => //; apply: (subsetP Hh1).
    have F13: K <| Gx by apply: normal_stab.
    case: (prim_trans_norm F10 F11 F12  F13) => Ksub; last first.
      apply: dvdn_trans (group_dvdn F8). 
      by rewrite -F7; apply: (@trans_div _ _ (perm_act d) _ _ _ Hy).
    have F14: faithful (perm_act d) Gx (setD1 (setA d) x).
      apply/faithfulP => g Hg.
      apply: (faithfulP _ _ _ (perm_act_faithful d)) => z Hz.
      case: (Hg _ Hy); case/stabiliserP => Hag Hx1 Hy1; split => //.
      case E1: (x == z); first by rewrite -(eqP E1).
      by case: (Hg z); rewrite // /setD1 E1.
    have Hreg: forall g (z: d), H g -> g z = z -> g = 1.
      have F15: forall g, H g -> g x = x -> g = 1.
        move => g Hg Hgx.
        have F15: card K <= 1.
          rewrite /faithful /= in F14; rewrite -(eqP F14).
          by apply: subset_leq_card.
        have F16: K g by  apply/stabiliserP; split.
        apply: sym_equal; apply/eqP; move: F15; rewrite (cardD1 1) group1 (cardD1 g) /setD1 F16.
        by case (1 == g).   
      move=> g z Hg Hgz.
      have: (setA d x) by done.
      rewrite -(F3 z) //; case /iimageP => g1 Hg1 Hg2.
      apply: (mulg_injl g1^-1); apply: (mulg_injr g1); gsimpl.
      apply: F15; first by rewrite -sconjgE (normalP _ _ Hh2) // groupV.
      change (perm_act d x (g1^-1 * g * g1) = x).
      by rewrite Hg2 -act_morph; gsimpl; rewrite act_morph {2}/perm_act /to /= Hgz.
    clear K F8 F12 F13 Ksub F14.
    case: (cauchy (tp: prime 5) F6) => h; case/andP => Hh Horder.
    have diff_hnx_x: forall n, 0 < n -> n < 5 -> (h ** n) x != x.
      move => n Hn1 Hn2; apply/negP => HH.
      have: orderg (h ** n) = 5.
        rewrite orderg_gcd // (eqP Horder).
        by move: Hn1 Hn2; clear HH; do 5 (case: n => [|n] //).
      have Hhd2: H (h ** n) by rewrite groupE.
      by rewrite (Hreg _ _ Hhd2 (eqP HH)) orderg1.
    pose S1 := Seq x (h x) ((h ** 3) x).
    have size_S1: size S1 = card (setA I_(3)) by rewrite card_ordinal.
    have distinct_S1: (distinctb (Fgraph size_S1)).
      rewrite /distinctb /= /setU1 orbF andbT; apply/eqP.
      have: h x != x by rewrite -(gexpn1 h) diff_hnx_x. 
      case: (_ == x) => // _.
      have: (h ** 3) x != x by exact: diff_hnx_x.
      rewrite /=; case: (_ == x) => // _.
      have: h ((h ** 2) x) != h x.
        apply/negP => HH.
        have: (h ** 2) x != x by exact: diff_hnx_x.
        case/negP; apply/eqP; exact: (perm_inj (eqP HH)).
      by rewrite /= mulg1 -!permM !mulgA; case: (_ == h x) => // _.
    have lift_S1: dlift (setA d) (EqSig _ _ distinct_S1) by
     apply/allP => z; case/or3P => //; move/eqP => <-.
    pose S2 := Seq x (h x) ((h ** 2) x).
    have size_S2: size S2 = card (setA I_(3)) by rewrite card_ordinal.
    have distinct_S2: (distinctb (Fgraph size_S2)).
      rewrite /distinctb /= /setU1 orbF andbT; apply/eqP.
      have: h x != x by rewrite -(gexpn1 h) diff_hnx_x. 
      case: (_ == x) => // _.
      have: (h ** 2) x != x by exact: diff_hnx_x.
      rewrite /=; case: (_ == x) => // _.
      have: h ((h ** 1) x) != h x.
        apply/negP => HH.
        have: (h ** 1) x != x by exact: diff_hnx_x.
        by case/negP; apply/eqP; exact: (perm_inj (eqP HH)).
      by rewrite /= mulg1 -!permM; case: (_ == h x) => // _.
    have lift_S2: dlift (setA d) (EqSig _ _ distinct_S2) by
      apply/allP => z; case/or3P => //; move/eqP => <-.
    case: F2 => F2 Fc.
    rewrite -(F2 _ lift_S1) in lift_S2; case/iimageP: lift_S2 => g Hg.
    move/val_eqP; move/eqP; move/fgraph_eqP.
    rewrite /perm_act /= /to; case/and4P => Hgx Hghx Hgh2x _.
    have h_g_com: h * g = g * h.
      suff HH: (g * h * g^-1) * h^-1 = 1 by rewrite -[h * g]mul1g -HH; gsimpl.
      apply: (Hreg _ x); last by rewrite !permM -(eqP Hgx) (eqP Hghx) -!permM; gsimpl; rewrite perm1.
      rewrite groupM // ?groupV //.
      have Hgm1: alt d (g ^-1) by rewrite groupV.
      by rewrite -(normalP _ _ Hh2 g^-1 Hgm1) s2f /conjg; gsimpl.
    have: (g * (h ** 2) * g ^-1) x = (h ** 3) x.
      rewrite !permM !perm1 -(eqP Hgx).
      have ->: h (h x) = (h ** 2) x by rewrite /= permM mulg1.
      by rewrite {1}(eqP Hgh2x) -!permM /=; gsimpl.
    have ->: g * (h ** 2) = (h ** 2) * g
      by rewrite /= mulg1 mulgA -h_g_com -mulgA -h_g_com mulgA.
    gsimpl; have ->: h ** 3 = h * (h ** 2) by rewrite /=; gsimpl.
    rewrite permM; move/(perm_inj) => HH.
    case/negP: (diff_hnx_x 1%N tp tp).
    by rewrite gexpn1 -HH.
  by rewrite (@gauss_inv 4 5) // F7.
apply/simpleP => H Hh1 Hh2.
case Hcard1: (card H == 1%N); move/eqP: Hcard1 => Hcard1.
  left; apply fsym; apply/subset_cardP; first by rewrite card1.
  by apply/subsetP => z; move/eqP => <-; exact: group1.
case Hcard60: (card H == 60%N); move/eqP: Hcard60 => Hcard60.
  by right; apply/subset_cardP => //; rewrite F1.
have Hcard20: card H = 20; last clear Hcard1 Hcard60.
  have Hdiv: dvdn 20 (card H).
    apply: FF => //.
    by move => HH; case: Hcard1; apply: eq_card_trans HH; exact: card1.
  case H20: (card H == 20); first by apply/eqP.
  case Hcard60; move: (group_dvdn Hh1); rewrite F1 => Hdiv1.
  move: H20 Hdiv1 (dvdn_leq (tp: 0 < 60) Hdiv1) (pos_card_group H).
  by case/dvdnP: Hdiv; (do 4 (case => [-> |] //)) => n ->.
have prime_5: prime 5 by done.
have Hlogn: 0 < logn 5 (card H) by rewrite Hcard20  -[20]/(5^1*4)%N logn_mul.
case: (sylow1_cor prime_5 Hlogn) => S sylow_S.
have card_gsylow: card (gsylow 5 H) = 1%N.
  move: (sylow3_div prime_5 Hlogn) (sylow3_mod prime_5 Hlogn).
  rewrite Hcard20; case: (card _) => // n Hdiv.
  move: (dvdn_leq  (tp: (0 < 20)%N) Hdiv).
  by move: (n) Hdiv; do 20 (case => //).
case/andP: (sylow_S) => sub_S; rewrite Hcard20 => card_S.
suff: dvdn 20 (card S).
  by case/andP: sylow_S; rewrite Hcard20 => _; move/eqP => ->.
apply FF; first (by apply: (subset_trans sub_S)); try 
   by move => HH; move: card_S; rewrite (eq_card HH) ?F1 ?card1.
apply/normalP => g Hg.
have conj_sub: subset (S :^ g) H.
  move/normalP: Hh2; move /(_ g Hg) => <-.
  by apply/subsetP => g1; rewrite !s2f => HH; apply: (subsetP sub_S).
have HH: gsylow 5 H {(S :^ g) as group _}.
  by rewrite /gsylow /sylow conj_sub card_sconjg Hcard20.
suff Hs: {S :^ g as group _} = S by rewrite -{2}Hs.
apply/eqP; move: card_gsylow.
rewrite (cardD1 {(S :^g) as group _}) HH (cardD1 S) /setD1 /gsylow sylow_S /=.
by case: (_ == _).
Qed.

Section Restrict.

Variable d: finType.
Variable x: d.
Let d' := sub_finType (setC (set1 x)).

Section oneF.

Variable f: d -> d.
Hypothesis inj_f: injective f.

Definition f1 (x1: d'):=
match x1 with
| EqSig x1 _ => 
  if (f x == x) then f x1 else x1
end.

Lemma f1_d': forall x1, setC (set1 x) (f1 x1).
Proof.
move=> [x1 Hx1]; rewrite /f1.
case E0: (_ == _); move: E0; move/eqP => // E0.
apply/negPn => HH; case/negP: Hx1; apply/eqP; apply: inj_f.
by rewrite -(eqP HH).
Qed.

Definition fl (x1: d'): d':= 
  EqSig (setC (set1 x)) (f1 x1) (f1_d' x1).

Lemma inj_fl: injective fl.
Proof.
move=> [x1 Hx1] [y1 Hy1]; move/eqP; rewrite /fl /f1 {1}/set1 /=; move/eqP => HH.
apply/eqP; rewrite /set1 /=; apply/eqP; move: HH.
case E0: (_ == x); move/eqP: E0 => E0 // E1.
by apply: inj_f.
Qed.

Variable g: d' -> d'.
Hypothesis inj_g: injective g.

Definition gl (x1: d):=
  if pick (fun z => val z == x1) is Some y1 then val (g y1) else x.

Lemma inj_gl: injective gl.
Proof.
move=> x1 y1; rewrite /gl /=.
do 2 case pickP.
- move=> x2 Hx2 y2 Hy2; rewrite -(eqP Hx2) -(eqP Hy2).
  move/eqP; move/val_eqP => Hxy.
  by apply/eqP; apply/val_eqP; apply inj_g.
- by move=> _ y _; case (g y); rewrite /setC /= => z Hz Hz1; case/negP: Hz; rewrite Hz1.
- by move=> y _ _; case (g y); rewrite /setC /= => z Hz Hz1; case/negP: Hz; rewrite Hz1.
move => Hx2 Hy2 _.
have <-: x = x1.
  apply/eqP; case E1: (_ == _) => //.
  move/eqP: E1; move/eqP => E1.
  by move: (Hy2 (EqSig (setC (set1 x)) _ E1)); rewrite /= eq_refl.
apply/eqP; case E1: (_ == _) => //.
move/eqP: E1; move/eqP => E1.
by move: (Hx2 (EqSig (setC (set1 x)) _ E1)); rewrite /= eq_refl.
Qed.

Lemma gl_x: gl x = x.
Proof.
rewrite /gl; case pickP => //. 
by case => v /= Hv Hv1; case/negP: Hv; rewrite eq_sym.
Qed.

End oneF.

Definition rfd (p: permType d):  permType d' :=
match p with
| Perm (EqSig f Hf) =>
    let g := fl (perm_uniqP f Hf) in
    let Hg := perm_of_injP (@inj_fl _ (perm_uniqP f Hf)) in
       Perm (EqSig _ (fgraph_of_fun g) Hg)
end.

Lemma rfd_val: forall (p: permType d) y, p x = x -> val (rfd p y) = p (val y).
Proof.
case; case => f Hf; case => y; rewrite /setC => Hy /=.
by rewrite p2f /fl /fun_of_perm /=; move => ->; rewrite eq_refl.
Qed.

Lemma rfd1: rfd 1 = 1.
Proof.
apply eq_fun_of_perm => [[z Hz]]; rewrite p2f /fl /f1 perm1.
by apply/val_eqP => /=; rewrite !g2f eq_refl.
Qed.

Lemma rfd_is_id: forall p: permType d, p x  <> x -> rfd p = 1.
Proof.
case; case => gr Ugr Igr.
apply: eq_fun_of_perm => [[z Hz]]; rewrite p2f /rfd /= perm1.
by apply/val_eqP => /=; case E1: (_ == x); move/eqP: E1 => E1.
Qed.

Hypothesis card_d: 2 < card (setA d).

Definition rfd_dom: dom rfd = stabiliser (perm_act d) (perm_finType d) x.
Proof.
apply/isetP => p; apply/isetUP/stabiliserP.
  case; [move/kerP | rewrite s2f]; rewrite !s2f.
    move=> HH; split=> //.
    apply/eqP; case E0: (_ == _); move/eqP: E0 => // E0.
    case Ex: (set0b (setD1 (setD1 (setA d) x) (p x))).
      move: card_d; rewrite (cardD1 x) (cardD1 (p x)).
      by rewrite /set0b in Ex; rewrite (eqP Ex); case setA; case: setD1.
    case/set0Pn: Ex => z; case/andP => diff_px_z; case/andP => diff_x_z Hz.
    move: (HH (transp x (p x))); rewrite [rfd (transp _ _)]rfd_is_id => // HH1; last first.
     by rewrite /= /to transpL in HH1; case E0.
    have diff_x_pmx: x != p^-1 x.
      by apply/eqP => Hx; case/eqP: E0; rewrite /= /to {1}Hx -permM mulVg perm1 eq_refl.
    case/eqP: diff_px_z.
    have ->: p x = p^-1 x.
      have ->: p^-1 x = val ((1: perm_finGroupType d') (EqSig (setC (set1 x)) _ diff_x_pmx)) by rewrite perm1.
      rewrite -HH1 rfd_val /= permM //; last by rewrite transpR.
      by rewrite -[@fun_of_perm d p (@fun_of_perm _ _ _)]permM mulVg perm1 transpL.
    move: (HH (transp x (p x) * (transp (p x) z))); rewrite [rfd (transp _ _ * _)]rfd_is_id => HH2; last first.
      by rewrite /= /to permM !transpL in HH2; case/eqP: diff_x_z.
    have ->: p^-1 x = val ((1: perm_finGroupType d') (EqSig (setC (set1 x)) _ diff_x_pmx)) by rewrite perm1.
    rewrite -HH2 rfd_val /= permM //.
      by rewrite -[@fun_of_perm d p (@fun_of_perm _ _ _)]permM mulVg perm1 permM !transpL.
    rewrite permM transpR transpD //; first by move/eqP: E0.
    by rewrite eq_sym.
  move => HH; split => //; apply/eqP; case E0: (_ == _); move/eqP: E0 => E0 //.
  case/eqP: HH.
  case: p E0; case => gr Ugr Igr.
  apply: eq_fun_of_perm => [[z Hz]]; rewrite p2f /rfd /= perm1.
  by apply/val_eqP => /=; case E1: (_ == x); move/eqP: E1 => E1.
case => _ Hx; rewrite s2f.
case E0: (_ == _); move/eqP: E0 => E0; last by right.
suff ->: p = 1 by left; apply/kerP=> y; rewrite mul1g.
apply: eq_fun_of_perm => z; rewrite perm1.
case Ez: (x == z); first by rewrite -(eqP Ez).
move/eqP: Ez; move/eqP => Ez.
have ->: z = val ((EqSig (setC (set1 x)) _ Ez)) by done.
by rewrite -rfd_val // E0 perm1.
Qed.

Definition rfd_morph: morphism (perm_finGroupType d) (perm_finGroupType d').
exists rfd.
  rewrite rfd_dom.
  exact: (@group_set_stab _ _ (perm_act d) (groupA (perm_finGroupType d))).
move=> x1 y1; rewrite rfd_dom; case/stabiliserP=> _ Hx1; case/stabiliserP=> _ Hy1.
rewrite /perm_act /to /= in Hx1 Hy1.
have Hxy1: (x1 * y1) x = x by rewrite permM Hx1.
apply: eq_fun_of_perm => z.
apply/val_eqP; rewrite rfd_val //.
by rewrite !permM !rfd_val.
Defined.

Definition rgd (p: permType d'):  permType d :=
match p with
| Perm (EqSig f Hf) =>
       Perm
         (EqSig (fun g : fgraphType d d => uniq (fval g))
            (fgraph_of_fun (x:=d) (x0:=d) (gl f))
           (perm_of_injP (d:=d) (inj_gl (perm_uniqP f Hf))))
end.

Lemma rgd_x: forall p, rgd p x = x.
Proof.
case; case=> f Hf /=.
by rewrite p2f gl_x.
Qed.

Lemma rfd_rgd: forall p, rfd (rgd p) = p.
Proof.
case; case=> f Hf /=.
apply: eq_fun_of_perm => [[z Hz]] /=.
rewrite p2f /fl /gl /f1 /fun_of_perm.
apply/val_eqP; rewrite /= !g2f.
case pickP.
  case; rewrite /setC /= => x1 Hx1 Hzx.
  by case/negP: Hx1; rewrite eq_sym.
rewrite eq_refl; case pickP.
  case; rewrite /setC /= => x1 Hx1 Hzx _.
  by apply/eqP; congr val; congr fun_of_fgraph; apply/val_eqP.
by move/(_ (EqSig (setC (set1 x)) _ Hz))=> /=; rewrite eq_refl.
Qed.

Lemma rfd_odd: forall p: permType d, p x = x -> odd_perm (rfd p) = odd_perm p.
Proof.
have HP0: forall p : permType  d, card {x : d, p x != x} = 0 -> odd_perm (rfd p) = odd_perm p.
  move => p Hp; suff ->: p = 1 by rewrite rfd1 !odd_perm1.
  apply: eq_fun_of_perm => z; rewrite perm1.
  suff: {x : d, p x != x} z = false; first by rewrite s2f; move/eqP.
  by rewrite (card0_eq Hp).
move=> p; elim: (card _) {-2}p (leqnn (card {x, p x != x})) => {p}[| n Hrec] p Hp Hpx.
  by apply: HP0; move: Hp; case: card.
case Ex: (set0b {x : d, p x != x}); first by apply: HP0; move: Ex; rewrite /set0b; move/eqP.
case/set0Pn: Ex => x1; rewrite s2f => Hx1.
have Hxx1:  x != x1 by apply/negP => HH; case/negP: Hx1; rewrite -(eqP HH) Hpx.
have Hpxx1: p x != x1 by apply/negP => HH; case/negP: Hx1; rewrite -(eqP HH) !Hpx.
have Hpx1x: x != p x1.
   by apply/negP => HH; case/negP: Hxx1; apply/eqP; apply (@perm_inj _ p); rewrite -(eqP HH).
pose p1 := p * transp x1 (p x1).
have Hp1: p1 x = x.
  rewrite /p1 permM; case transpP => //; first by move=> HH; case/negP: Hx1; rewrite -HH !Hpx.
  by move=> HH; apply: (@perm_inj _ p).
have Hcp1: card {x : d, p1 x != x} <= n.
  have F1: forall y, p y = y -> p1 y = y.
    move=> y Hy; rewrite /p1 permM Hy.
    case transpP => //; first by move => <-.
    by move=> Hpx1; apply: (@perm_inj _ p); rewrite -Hpx1.  
  have F2: p1 x1 = x1 by rewrite /p1 permM transpR.
  have F3: subset {x : d, p1 x != x} (setD1 {x : d, p x != x} x1).
    apply/subsetP => z; rewrite s2f /p1 permM.
    case transpP => HH1 HH2; rewrite /setD1 s2f.
    - case E1: (_ == _); first by case/negP: Hx1; rewrite {1}(eqP E1) HH1.
      by rewrite HH1 E1.
    - by case/negP: HH2; apply/eqP; apply: (@perm_inj _ p).
    by move => ->; rewrite andbT; apply/eqP => HH3; case HH2; rewrite HH3.
  apply: (leq_trans (subset_leq_card F3)).
  by move: Hp; rewrite (cardD1 x1) s2f Hx1.
have ->: p = p1 * transp x1 (p x1) by rewrite /p1 -mulgA transp2 mulg1.
rewrite odd_permM odd_transp eq_sym Hx1 (@morphM _ _ (rfd_morph)) ?rfd_dom; last 2 first.
- by apply/stabiliserP; split.
- apply/stabiliserP; split=> //.
  rewrite /= /to; case transpP => //.
    by move=> HH; case/negP: Hx1; rewrite -HH Hpx.
  by move=> HH; apply: (@perm_inj _ p); rewrite -HH.
rewrite -[rfd_morph _]/(rfd _) odd_permM Hrec //.
rewrite -[rfd_morph _]/(rfd _); first congr addb.
pose x2: d' := (EqSig (setC (set1 x)) _ Hxx1).
pose px2: d' := (EqSig (setC (set1 x)) _ Hpx1x).
suff ->: rfd (transp x1 (p x1)) = transp x2 px2.
  rewrite odd_transp /x2 /px2; apply/eqP; move/val_eqP => /=.
  by rewrite eq_sym => HH; case/negP: Hx1.
apply: eq_fun_of_perm => z.
have F1: transp x1 (p x1) x = x by rewrite transpD // eq_sym.
apply/val_eqP; rewrite rfd_val //.
case: (@transpP _ x2).
- by move=> ->; rewrite /x2 transpL.
- by move=> ->; rewrite /x2 transpR.
move=> HH1 HH2; rewrite transpD //.
  by apply/negP => HH3; case HH1; apply/val_eqP; rewrite -(eqP HH3).
by apply/negP => HH3; case HH2; apply/val_eqP; rewrite -(eqP HH3).
Qed.

Lemma rfd_iso: isog (stabiliser  (perm_act d) (alt d) x) (alt d').
Proof.
exists rfd_morph.
apply/andP; split.
  apply/eqP; apply/isetP=> z; apply/iimageP/idP.
    case=> p; case/stabiliserP; move/altP => Hp Hp1 ->; apply/altP.
    by rewrite /even_perm rfd_odd.
  move=> Hz; exists (rgd z); last by rewrite /= rfd_rgd.
  apply/stabiliserP; split.
    apply/altP; rewrite /even_perm -rfd_odd ?rgd_x //.
    by rewrite rfd_rgd; case/altP: Hz.
  by rewrite /= /to rgd_x. 
apply/injmP=> x1 y1; case/stabiliserP=> Hax1 Hx1; case/stabiliserP=> Hay1 Hy1 /= Hr.
rewrite /perm_act /to /= in Hx1 Hy1.
apply: eq_fun_of_perm => z.
case Ez: (x == z); move/eqP: Ez => Ez; first by rewrite -Ez Hy1.
move/eqP: Ez => Ez.
have ->: z = val ((EqSig (setC (set1 x)) _ Ez)) by done.
by rewrite -!rfd_val // Hr.
Qed.

End Restrict.

Lemma simple_alt5: forall d: finType, card (setA d) >= 5 -> simple (alt d).
Proof.
suff F1: forall n (d: finType), card (setA d) = n + 5 -> simple (alt d).
  move=> d H; apply: (F1 (card (setA d) - 5)).
  by rewrite addnC leq_add_sub.
elim => [| n Hrec d Hde]; first by exact: simple_alt5_base.
have Hd: 5 < card (setA d) by rewrite Hde addnC.
apply/simpleP => H Hh1 Hh2.
case E1: (set0b (setA d)); first by rewrite /set0b in E1; rewrite (eqP E1) in Hd.
case/set0Pn: E1 => x Hx.
have F2: ntransitive (perm_act d) (alt d) (setA d) 4.
  apply: ntransitive_weak (alt_trans d).
  by apply: (@ltn_sub2r 2 5) => //; apply: ltn_trans Hd.
have F3 := ntransitive1 (tp: 0 < 4) F2.
have F4 := ntransitive_primitive (tp: 1 < 4) F2.
case Hcard1: (card H == 1%N); move/eqP: Hcard1 => Hcard1.
  left; apply fsym; apply/subset_cardP; first by rewrite card1.
  by apply/subsetP => z; move/eqP => <-; exact: group1.
right.
case: (prim_trans_norm F3 F4 Hh1 Hh2) => F5.
  move: (perm_act_faithful d); rewrite /faithful; move/eqP => FC.
  by case: Hcard1; apply/eqP; rewrite eqn_leq -{1}FC subset_leq_card // (cardD1 1) group1.
case E1: (set0b (setD1 (setA d) x)).
  rewrite /set0b in E1; move: Hd.
  by rewrite (cardD1 x) (eqP E1); case: (setA d x).
case/set0Pn: E1 => y Hdy; case/andP: (Hdy) => diff_x_y Hy.
pose K := stabiliser (perm_act d) H x.
have F8: subset K H by apply: subset_stab.
pose Gx := stabiliser (perm_act d) (alt d) x.
have F9: ntransitive (perm_act d) Gx (setD1 (setA d) x) (4 - 1) by apply:  stab_ntransitive.
have F10: transitive (perm_act d) Gx (setD1 (setA d) x).
 by apply:  (ntransitive1 (refl_equal true: 0 < 3)).
have F11: primitive (perm_act d) Gx (setD1 (setA d) x)
  by apply: (ntransitive_primitive (refl_equal true: 1 < 3)).
have F12: subset K Gx.
  apply/subsetP=> g; case/stabiliserP => Hg Hperm.
  by apply/stabiliserP; split => //; apply: (subsetP Hh1).
have F13: K <| Gx by apply: normal_stab.
case: (@prim_trans_norm _ _ _ {Gx as group _} _ F10 {K as group _} F11 F12 F13) => Ksub; last first.
  have F14 := (subgroup_transitive Hx Hh1 F3 F5); rewrite -/Gx in F14.
  have Gx_simpl: simple Gx.
    have FF: 2 < card (setA d) by apply: (leq_trans _ Hd).
    apply: (isog_simpl (isog_sym (rfd_iso x FF))).
    apply: Hrec => /=; apply/eqP.
    by move/eqP: Hde; rewrite card_sub -(cardC (set1 x)) card1 !addSn add0n.
  move/simpleP: Gx_simpl; case/(_ {K as group _} F12 F13) => HH.
  case Ez: (set0b (setD1 (setD1 (setA d) x) y)).
    move: Hd; rewrite /set0b in Ez.
    by rewrite (cardD1 x) (cardD1 y) (eqP Ez) /setD1 Hx Hy diff_x_y.  
    case/set0Pn: Ez => z; case/andP => diff_y_z Hdz; case/andP: (Hdz) => diff_x_z Hz.
    move: Hdz; rewrite -(Ksub _ Hdy); case/iimageP => g; rewrite HH; move/eqP => <- HH1.
    by case/negP: diff_y_z; rewrite HH1 act_1.
  rewrite -F14; apply/subset_eqP; apply/andP; split; apply/subsetP => z.
    by move => Hz; apply/smulgP; exists (1: (perm_finGroupType d)) z; rewrite ?group1 // mul1g.
  by case/smulgP => t u Ht Hu ->; rewrite groupM // (subsetP F8) // HH.
have F14: faithful (perm_act d) Gx (setD1 (setA d) x).
  apply/faithfulP => g Hg.
  apply: (faithfulP _ _ _ (perm_act_faithful d)) => z Hz.
  case: (Hg _ Hdy); case/stabiliserP => Hag Hx1 Hy1; split => //.
  case E1: (x == z); first by rewrite -(eqP E1).
  by case: (Hg z); rewrite // /setD1 E1.
have Hreg: forall g (z: d), H g -> g z = z -> g = 1.
  have F15: forall g, H g -> g x = x -> g = 1.
    move => g Hg Hgx.
    have F15: card K <= 1.
      rewrite /faithful /= in F14; rewrite -(eqP F14).
      by apply: subset_leq_card.
    have F16: K g by  apply/stabiliserP; split.
    apply: sym_equal; apply/eqP; move: F15; rewrite (cardD1 1) group1 (cardD1 g) /setD1 F16.
    by case (1 == g).   
  move=> g z Hg Hgz.
  have: (setA d x) by done.
  rewrite -(F3 z) //; case /iimageP => g1 Hg1 Hg2.
  apply: (mulg_injl g1^-1); apply: (mulg_injr g1); gsimpl.
  apply: F15; first by rewrite -sconjgE (normalP _ _ Hh2) // groupV.
  change (perm_act d x (g1^-1 * g * g1) = x).
  by rewrite Hg2 -act_morph; gsimpl; rewrite act_morph {2}/perm_act /to /= Hgz.
clear K F8 F12 F13 Ksub F14.
have Hcard: 5 < card H.
  apply: (leq_trans Hd); apply dvdn_leq; first by exact: pos_card_group.
  apply: (trans_div Hx F5).
case Eh: (set0b (setD1 H 1)).
  by move: Hcard; rewrite /set0b in Eh; rewrite (cardD1 1) group1 (eqP Eh).
case/set0Pn: Eh => h; case/andP => diff_1_h Hh.
case Eg: (set0b (setD1 (setD1 (setD1 H 1) h) h^-1)).
  move: Hcard; rewrite /set0b in Eg.
  rewrite (cardD1 1) group1 (cardD1 h) (cardD1 h^-1) /setD1 diff_1_h Hh (eqP Eg).
  by set u := [&& _, _ & _]; case u.
case/set0Pn: Eg => g; case/andP => diff_h1_g; case/andP => diff_h_g; case/andP => diff_1_g Hg.
case diff_hx_x: (h x == x).
  by case/negP: diff_1_h; rewrite eq_sym; apply/eqP; apply: (Hreg _ _ Hh (eqP diff_hx_x)).
case diff_gx_x: (g x == x).
  case/negP: diff_1_g; rewrite eq_sym; apply/eqP; apply: (Hreg _ _ Hg (eqP diff_gx_x)).
case diff_gx_hx: (g x == h x).
  case/negP: diff_h_g; apply/eqP; apply: (mulg_injr g^-1); gsimpl.
  apply: (Hreg _ x); first by rewrite groupM // groupV.
  by rewrite permM -(eqP diff_gx_hx) -permM mulgV perm1.
case diff_hgx_x: ((h * g) x == x).
  case/negP: diff_h1_g; apply/eqP; apply: (mulg_injl h); gsimpl.
  by apply sym_equal; apply: (Hreg _ x); first (by exact: groupM); apply/eqP.
case diff_hgx_hx: ((h * g) x == h x).
  case/negP: diff_1_g; apply/eqP.
  by apply sym_equal; apply: (Hreg _ (h x)) => //; apply/eqP; rewrite -permM.
case diff_hgx_gx: ((h * g) x == g x).
  by case/eqP: diff_hx_x; apply: (@perm_inj _ g) => //; apply/eqP; rewrite -permM.
case Ez: (set0b (setD1 (setD1 (setD1 (setD1 (setA d) x) (h x)) (g x)) ((h * g) x))).
  move: Hd; rewrite /set0b in Ez.
  rewrite (cardD1 x) (cardD1 (h x)) (cardD1 (g x)) (cardD1 ((h * g) x)) (eqP Ez) Hx.
  by do 3 (case: (setD1 _)).
case/set0Pn: Ez => z; case/andP => diff_hgx_z; case/andP => diff_gx_z;
  case/andP => diff_hx_z; case/andP => diff_x_z Hz.
pose S1 := Seq x (h x) (g x) z.
have size_S1: size S1 = card (setA I_(4)) by rewrite card_ordinal.
have distinct_S1: (distinctb (Fgraph size_S1)).
  rewrite /distinctb /= /setU1 orbF andbT; apply/eqP.
  rewrite diff_hx_x diff_gx_x diff_gx_hx !(eq_sym z) diff_x_z.
  move: diff_hx_z diff_gx_z; do 2 (case: (_ == _) => //).
have lift_S1: dlift (setA d) (EqSig _ _ distinct_S1).
  by apply/allP => z1; case/or4P => //; move/eqP => <-.
pose S2 := Seq x (h x) (g x) ((h * g) x).
have size_S2: size S2 = card (setA I_(4)) by rewrite card_ordinal.
have distinct_S2: (distinctb (Fgraph size_S2)).
  rewrite /distinctb /= /setU1 orbF andbT; apply/eqP.
  by rewrite diff_hx_x diff_gx_x diff_hgx_x diff_gx_hx diff_hgx_hx diff_hgx_gx.
have lift_S2: dlift (setA d) (EqSig _ _ distinct_S2)
  by apply/allP => z1; case/or4P => //; move/eqP => <-.
case: F2 => F2 Fc.
rewrite -(F2 _ lift_S1) in lift_S2; case/iimageP: lift_S2 => k Hk.
move/val_eqP; move/eqP; move/fgraph_eqP.
rewrite /perm_act /= /to; case/and5P => Hkx Hkhx Hkgx Hkhgx _.
have Hkm1: alt d (k ^-1) by rewrite groupV.
have h_k_com: h * k = k * h.
  suff HH: (k * h * k^-1) * h^-1 = 1 by rewrite -[h * k]mul1g -HH; gsimpl.
  apply: (Hreg _ x); last by rewrite !permM -(eqP Hkx) (eqP Hkhx) -!permM; gsimpl; rewrite perm1.
  rewrite groupM // ?groupV //.
  by rewrite -(normalP _ _ Hh2 k^-1 Hkm1) s2f /conjg; gsimpl.
have g_k_com: g * k = k * g.
  suff HH: (k * g * k^-1) * g^-1 = 1 by rewrite -[g * k]mul1g -HH; gsimpl.
  apply: (Hreg _ x); last by rewrite !permM -(eqP Hkx) (eqP Hkgx) -!permM; gsimpl; rewrite perm1.
  rewrite groupM // ?groupV //.
  by rewrite -(normalP _ _ Hh2 k^-1 Hkm1) s2f /conjg; gsimpl.
have HH: (k * (h * g) * k ^-1) x = z.
   by rewrite 2!permM -(eqP Hkx) (eqP Hkhgx) -permM mulgV perm1.
case/negP: diff_hgx_z.
by rewrite -HH !mulgA -h_k_com -!mulgA [k * _]mulgA -g_k_com -!mulgA mulgV mulg1.
Qed.
