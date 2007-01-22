Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import div.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Action.

Open Scope group_scope.

Variable (G: finGroupType) (H : setType G).
Hypothesis group_H: group H.
Variable S: finType.

Variable to : G -> S -> S.
Hypothesis to_1: forall x, to 1 x = x.
Hypothesis to_morph : forall (x y:G) z,
  H x -> H y -> to (x * y) z = to x (to y z).

Lemma to_bij : forall x, H x -> bijective (to x).
Proof.
move => x Hx.
apply: fin_inj_bij.
apply: (@can_inj _ _ (to x) (to x^-1)) => a.
by rewrite -to_morph ?groupV // mulVg to_1.
Qed.

Definition orbit a := image (fun z => to z a) H.

Lemma orbit_to: forall a x, H x -> orbit a (to x a).
Proof.
by move => a x Hx; exact: image_f_imp.
Qed.

Lemma orbit_refl : forall x, orbit x x.
Proof.
move=> x; rewrite /orbit -{2}(to_1 x).
by apply: image_f_imp; rewrite group1.
Qed.

Lemma orbit_sym : forall x y, orbit x y = orbit y x.
Proof.
move => x y; rewrite /orbit [image]lock; apply/idP/idP; 
  unlock => H1.
  rewrite -(to_1 x) -(mulVg (diinv H1)).
  by rewrite -{1}(f_diinv H1) to_morph; try apply: image_f_imp;
     rewrite ?groupV // a_diinv.
rewrite -(to_1 y) -(mulVg (diinv H1)).
by rewrite -{1}(f_diinv H1) to_morph; try apply: image_f_imp;
   rewrite ?groupV // a_diinv.
Qed.

Lemma orbit_trans : forall x y, connect orbit x y = orbit x y.
Proof.
move=> x y; apply/idP/idP; last exact: connect1.
move/connectP=> [p Hp <- {y}]; rewrite orbit_sym.
elim: p x Hp => [|y p IHp] x /=; first by rewrite orbit_refl.
move/andP=> [Hxy Hp].
move: (IHp _ Hp) => H1.
rewrite orbit_sym in H1; rewrite -(f_diinv H1).
rewrite orbit_sym in Hxy; rewrite -(f_diinv Hxy).
rewrite -{5}(to_1 y) -(mulVg (diinv H1)).
set (k :=  (diinv H1)).
set (k1 :=  (diinv Hxy)).
have F1: (H k) by apply (a_diinv H1).
have F2: (H k1) by apply (a_diinv Hxy).
rewrite to_morph //; last rewrite groupV => //.
rewrite -to_morph //; last rewrite groupV => //.
apply: image_f_imp.
by apply: groupM => //; rewrite groupV.
Qed.

Lemma orbit_csym : connect_sym orbit.
Proof. by move=> x y; rewrite !orbit_trans orbit_sym. Qed.

Definition stabilizer a := {x, H x && (to x a == a)}.

Definition SO a := H == stabilizer a.

Lemma stabilizerP: forall a x, reflect (to x a = a /\ H x) (stabilizer a x).
Proof.
move => a x; apply: (iffP idP).
  by rewrite /stabilizer s2f; move/andP => [Htox Hx];split;[apply/eqP|].
by rewrite /stabilizer s2f; move=>[-> ->]; rewrite eq_refl andbT.
Qed.

Lemma orbitP: forall x a, reflect (exists2 z, H z & to z a = x) (orbit a x).
Proof.
move => x a; apply: (iffP idP) => H1.
  exists (diinv H1); first exact: a_diinv.
  exact: (@f_diinv _ _ (fun z => to z a)).
rewrite /orbit.
by case: H1 => c Hc <-; apply: image_f_imp.
Qed.

Lemma SOP : forall a, reflect (orbit a =1 set1 a) (SO a).
Proof.
move => a; apply:(iffP eqP).
  move => Hstab x; apply /orbitP.
  case Dx: (a == x); first by exists (Group.unit G); rewrite ?to_1 ?group1 ?(eqP Dx).
  move => [c Hc Htoc]; rewrite Hstab in Hc; move/stabilizerP: Hc => [Htoc' Hx].
  by rewrite Htoc in Htoc'; rewrite Htoc' eq_refl in Dx.
move => Ho; apply: iset_eq => x; rewrite s2f.
case Hx: (H x) => //; rewrite andTb.
rewrite eq_sym -(Ho (to x a)); symmetry; apply/orbitP.
exists x => //.
Qed.

Lemma stab_1: forall a, stabilizer a 1.
Proof. by move => a; apply/stabilizerP; split; [ apply to_1 | apply group1 ]. Qed.

Lemma group_stab : forall a, group (stabilizer a).
Proof.
move => a.
apply/groupP; split; first by apply stab_1.
move => x y; move/stabilizerP => [Htox Hx];move/stabilizerP => [Htoy Hy].
by apply/stabilizerP; rewrite to_morph ?Htoy ?Htox ?groupMl; try split.
Qed.

Lemma subset_stab : forall a, subset (stabilizer a) H.
Proof. by move => a; apply/subsetP => x; move/stabilizerP => [_ Hx]. Qed.

Lemma card_orbit: forall a, card (orbit a) = indexg (stabilizer a) H.
Proof.
move => a. 
rewrite -lcoset_indexg //; last exact: subset_stab;
  last exact: group_stab.
rewrite /n_comp; move: (group_stab a) => Hsb.
set c := (fun x : G => {y : G, stabilizer a (x^-1 * y)}).
set rs := roots c.
have F1: dinjective (setI rs H) (fun z => to z a).
  move => x y Hx Hy /= Ht.
  case/andP: Hx => Hx1 Hx2.
  case/andP: Hy => Hy1 Hy2.
  rewrite -(eqP Hx1) -(eqP Hy1).
  apply/rootP => //; first exact: lcoset_csym.
  rewrite /c connect_lcoset /lcoset; last exact: group_stab.  
  have F1: H (x^-1 * y) by rewrite groupM // groupV.
  rewrite s2f; apply/stabilizerP; split => //.
  apply/eqP; rewrite -(bij_eq (to_bij Hx2)).
  by rewrite Ht -to_morph; gsimpl.
rewrite -(card_dimage F1).
apply eq_card.
move => x; apply/orbitP/imageP.
  case => y Hy <-.
  have F2: c y (root c y).
    by rewrite /c -connect_lcoset // connect_root.
  have F3: H (y^-1 * (root c y)).
    move/subsetP: (subset_stab a) => H1.
    by rewrite /sub_set in H1; apply: H1; rewrite s2f in F2.
  have F4: H (root c y).
    by rewrite -(@groupMl _ _ group_H y^-1) // groupV.
  exists (root c y).
    apply/andP; split => //.
    by apply: roots_root; exact: lcoset_csym.
  move: F2; rewrite s2f; case/stabilizerP => H1 _.
  rewrite -{1}H1 -to_morph //; gsimpl.
case => y; case/andP => Hy1 Hy2 ->.
rewrite /rs in Hy1.
by exists y.
Qed.

Lemma card_orbit_div: forall a, dvdn (card (orbit a)) (card H).
Proof.
move => a.
rewrite -(LaGrange (group_stab a)) //.
  by rewrite -(card_orbit a) dvdn_mull.
apply subset_stab.
Qed.

Variable n p: nat.
Hypothesis prime_p: prime p.
Hypothesis card_H: card H = (p ^ n)%N.

(***********************************************************************)
(*                                                                     *)
(*           The mod p lemma                                           *)
(*                                                                     *)
(***********************************************************************) 

Lemma mpl: modn (card (setA S)) p = modn (card SO) p.
Proof.
rewrite -(addn0 (card SO)) -(cardIC SO (setA S)) /setI.
rewrite -modn_add -[modn (_ + 0) _]modn_add; congr modn;
 congr addn; rewrite mod0n.
set (e := (fun x : S => (setA S) x && setC SO x)).
have C1: closed orbit e.
 move => x y; rewrite /e /=.
 case Eq1: (x == y); first by rewrite (eqP Eq1).
 move => H1; apply/negP/negP => H2 H3; case: H2.
   move: (SOP _ H3) => H4.
   by move: (H4 x); rewrite orbit_sym H1 eq_sym Eq1.
 move: (SOP _ H3) => H4.
 by move: (H4 y); rewrite H1 Eq1.
have C2: forall a, e a -> dvdn p (card (orbit a)).
  move => a Ha.
  have F1: (dvdn (card (orbit a)) (p ^ n))
    by rewrite -card_H card_orbit_div.
  move/(@dvdn_exp_prime _ _ _ prime_p): F1 => 
      [] [|m] /= H1 H2; last by rewrite H2 dvdn_mulr.
  unfold e in Ha; move/andP: Ha => [_ Ha].
  move/negP: Ha => Ha; case Ha.
  apply/SOP.
  have V1: (card (set1 a) = card (orbit a)).
    by apply sym_equal; rewrite card1.
  move => x; apply sym_equal; move: x.
  apply: (elimT (subset_cardP V1)).
  by apply/subsetP => x Hx; rewrite (eqP Hx) orbit_refl.
move Dn: (n_comp orbit e) => n1.
elim: n1 e C1 C2 Dn => [|n1 Rec] e C1 C2.
  move/eqP=> Hk0; rewrite -(mod0n p); congr modn.
  apply: (appP set0P eqP) => x; apply/idP=> Hx.
  case/idP: (set0P Hk0 (root orbit x)); rewrite /setI (roots_root orbit_csym).
  by rewrite -(closed_connect C1 (connect_root _ _)).
case: (pickP (setI (roots orbit) e));
 last by move => Hk; rewrite /n_comp (eq_card Hk) card0.
move => x Dn.
move: (andP Dn) => [H1 H2].
rewrite /n_comp (cardD1 x) Dn => [] [Dn1].
rewrite -(cardIC (orbit x) e).
rewrite -modn_add -(mod0n p) -(add0n 0) -[modn (0 + _) _]modn_add;
  congr modn; congr addn; rewrite mod0n.
  move: (C2 x H2); rewrite /dvdn; move/eqP => H3.
  rewrite -H3; congr modn.
  apply eq_card => z; rewrite /setI.
  case Eq1: (orbit x z); last by rewrite andbF.
  rewrite andbT (C1 z x) //  ?H2.
  by rewrite orbit_sym Eq1.
rewrite -{Rec}(Rec (setD e (orbit x)));
 first by congr modn; apply: eq_card => y; exact: andbC.
 move=> y z Hyz; rewrite /setD (C1 _ _ Hyz) -!orbit_trans.
 by rewrite (same_connect_r orbit_csym (connect1 Hyz)).
 by move => a; move/andP => [_ Ha]; apply C2.
apply: {n1}etrans Dn1; apply: eq_card => y; rewrite /setD1 /setI andbCA /setD.
rewrite -orbit_trans (sameP (rootP orbit_csym) eqP).
by case Dy: (roots orbit y) (andP Dn) => //= [] [Dx _]; rewrite (eqP Dy) (eqP Dx).
Qed.

End Action.

Section PermAction.

Open Scope group_scope.

Variable S : finType.
Let G := perm_finGroupType S.
Variable H : setType G.
Hypothesis group_H: group H.

Definition to (u : G) : permType S := u.

Lemma to_1 : forall x, to 1 x = x.
Proof.
move => x; rewrite /to /unitg /= /perm_unit /fun_of_perm /=.
by rewrite /comp can_fgraph_of_fun.
Qed.

Lemma to_morph : forall (x y:permType S) z,
  H x -> H y -> to (x * y) z = to x (to y z).
Proof. 
move => x y z Hx Hy /=.
rewrite /perm_mul /to /=.
by do 1!rewrite /fun_of_perm /= /comp can_fgraph_of_fun.
Qed.

End PermAction.

