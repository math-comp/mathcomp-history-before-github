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
Require Import group_perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Action.

Open Scope group_scope.

Variable (G: finGroupType) (H : setType G) (S:finType).
Hypothesis group_H: group H.

Variable to : S -> G -> S.
Hypothesis to_1 : forall x, to x 1 = x.
Hypothesis to_morph : forall (x y:G) z,
  H x -> H y -> to z (x * y) = to (to z x) y.

Lemma can_action : forall x, H x -> cancel (fun e => to e x) (fun e => to e x^-1).
Proof.
move => x Hx; rewrite/cancel => e.
rewrite -to_morph ?groupV //; gsimpl.
Qed.

Lemma to_bij : forall x, H x -> bijective (fun e => to e x).
Proof.
move => x Hx; exists (fun e => to e x^-1). 
  exact: can_action.
apply: canF_sym; exact: can_action.
Qed.

Variable a : S.

Definition orbit := (fun z => to a z) @: H.

Lemma orbitP: forall x, reflect (exists2 z, H z & to a z = x) (orbit x).
Proof.
by move=> x; apply: (iffP (@iimageP _ _ _ _ _)); case=> y; exists y.
Qed.

Lemma orbit_to: forall x, H x -> orbit (to a x).
Proof. by move=> x Hx; apply/orbitP; exists x. Qed.

Lemma orbit_refl : orbit a.
Proof. rewrite -[a]to_1; apply: orbit_to; exact: group1. Qed.

Definition stabilizer := {x, H x && (to a x == a)}.

Lemma stabilizerP: forall x, reflect (H x /\ to a x = a) (stabilizer x).
Proof.
by move=> x; rewrite s2f; apply: (iffP andP) => [] [Hx]; move/eqP.
Qed.

Definition SO := H == stabilizer.

Lemma SOP : reflect (orbit = {:a}) SO.
Proof.
apply: (iffP eqP) => [fixH | fix_a]; apply/isetP.
  move=> b; rewrite s2f; apply/idP/eqP=> [|<-]; last exact orbit_refl.
  by case/orbitP=> x; rewrite fixH s2f; case/andP=> _; move/eqP->.
move=>x; rewrite s2f; apply/idP/andP=> [Hx | [] //]; split=> //.
by have:= orbit_to Hx; rewrite fix_a s2f eq_sym.
Qed.

Lemma stab_1: stabilizer 1.
Proof. by apply/stabilizerP; split; [ apply group1 | apply to_1 ]. Qed.

Lemma group_stab : group stabilizer.
Proof.
apply/groupP; split; first by apply stab_1.
move => x y; move/stabilizerP => [Hx Htox];move/stabilizerP => [Hy Htoy].
apply/stabilizerP;split; first by rewrite groupMl.
by rewrite to_morph // Htox // Htoy. 
Qed.

Lemma subset_stab : subset stabilizer H.
Proof. by apply/subsetP => x; move/stabilizerP => [Hx _]. Qed.

Lemma to_repr_rcoset : forall z, H z -> to a (repr (stabilizer :* z)) = to a z.
Proof.    
move => z Hz; have:= repr_rcoset group_stab z.  
move/rcosetP=> [h Stabh ->].
move/stabilizerP:Stabh=>[Hh Htoh].
by rewrite to_morph // Htoh.
Qed.

Lemma card_orbit: card orbit = indexg stabilizer H.
Proof.
rewrite -card_sub /indexg.
set Sa := sub_finType _; pose f b := {x, H x && (to a x == b)}.
have injf: injective (fun u : Sa => f (val u)).
  move=> [b Hb] [c Hc] /= eq_f; apply: val_inj => /=; apply: eqP.
  case/orbitP: Hb {Hc} => [x Hx Dxa]; move/isetP: eq_f.
  by move/(_ x); rewrite !s2f Dxa Hx eq_refl.
have f_to: forall x, H x -> f (to a x) = stabilizer :* x. 
  move=> x Hx; apply/isetP=> y; have Hx1:= groupVr group_H Hx.
  rewrite !s2f groupMr //; case Hy: (H y) => //=. 
  rewrite -{4}(can_action Hx a) !to_morph // (@bij_eq _ (fun e => to e x^-1)) //; exact: to_bij.
rewrite -(card_image injf); apply: eq_card=> A.
apply/imageP/iimageP=> [[[b Hb] _] | [x Hx]] -> {A}/=.
  by case/orbitP: Hb => [x Hx <-]; exists x; rewrite // f_to.
by exists (EqSig _ (to a x) (orbit_to Hx)); rewrite //= f_to.
Qed.

Lemma card_orbit_div: dvdn (card orbit) (card H).
Proof.
rewrite -(LaGrange group_stab group_H subset_stab).
by rewrite -card_orbit dvdn_mull.
Qed.

Lemma card_orbit1 : card orbit = 1%N -> orbit = {:a}.
Proof.
move => CO; apply/isetP=> x; rewrite s2f.
case ax: (a == x).
  by apply/orbitP; exists (Group.unit G); rewrite ?group1 ?(eqP ax).
apply/negP; move=> Ox. 
have Oa := orbit_refl.
Admitted.

End Action.

Section ModP.

Variable (G: finGroupType) (H : setType G) (S:finType).
Hypothesis group_H: group H.
Variable to : S -> G -> S.
Hypothesis to_1: forall x, to x 1 = x.
Hypothesis to_morph : forall (x y:G) z,
  H x -> H y -> to z (x * y) = to (to z x) y.

(***********************************************************************)
(*                                                                     *)
(*           The mod p lemma                                           *)
(*                                                                     *)
(***********************************************************************) 


Lemma orbit_sym : forall x y, orbit H to x y = orbit H to y x.
Proof.
move => x y; rewrite /orbit; unlock iimage; rewrite !s2f; apply/idP/idP=>H1.
  rewrite -(to_1 x) -(mulgV (diinv H1)).
  by rewrite -{1}(f_diinv H1) to_morph; try apply: image_f_imp;
     rewrite ?groupV // a_diinv.
rewrite -(to_1 y) -(mulgV (diinv H1)).
by rewrite -{1}(f_diinv H1) to_morph; try apply: image_f_imp;
   rewrite ?groupV // a_diinv.
Qed.

Lemma orbit_trans : forall x y, connect (orbit H to) x y = (orbit H to) x y.
Proof.
move=> x y; apply/idP/idP; last by move =>*; apply: connect1.
move/connectP=> [p Hp <- {y}]; rewrite orbit_sym.
elim: p x Hp => [|y p IHp] x /=; first by rewrite orbit_refl.
move/andP=> [Hxy Hp].
move: (IHp _ Hp) => H1. rewrite -/orbit orbit_sym in Hxy.
rewrite orbit_sym /orbit in H1; unlock iimage in H1; rewrite s2f in H1. 
rewrite/orbit;unlock iimage;rewrite s2f -(f_diinv H1).
rewrite/orbit in Hxy;unlock iimage in Hxy;rewrite s2f in Hxy.
rewrite -(f_diinv Hxy) -{4}(to_1 y) -(mulgV (diinv H1)).
set (k :=  (diinv H1)).
set (k1 :=  (diinv Hxy)).
have F1: (H k) by apply (a_diinv H1).
have F2: (H k1) by apply (a_diinv Hxy).
rewrite to_morph //; last rewrite groupV => //.
rewrite -to_morph //; last rewrite groupV => //.
apply: image_f_imp.
by apply: groupM => //; rewrite groupV.
Qed.

Lemma orbit_csym : connect_sym (orbit H to).
Proof. by move=> x y; rewrite !orbit_trans orbit_sym. Qed.

Variable n p: nat.
Hypothesis prime_p: prime p.
Hypothesis card_H: card H = (p ^ n)%N.

Lemma mpl: modn (card (setA S)) p = modn (card (SO H to)) p.
Proof.
rewrite -(addn0 (card (SO _ _))) -(cardIC (SO H to) (setA S)) /setI.
rewrite -modn_add -[modn (_ + 0) _]modn_add; congr modn; congr addn; rewrite mod0n.
set (e := (fun x : S => (setA S) x && setC (SO H to) x)).
have C1: closed (orbit H to) e.
 move => x y; rewrite /e /=.
 case Eq1: (x == y); first by rewrite (eqP Eq1).
 move => H1; apply/negP/negP => H2 H3; case: H2.
   move: (SOP group_H to_1 _ H3) => H4; move/isetP:H4=>H4.
   by move: (H4 x); rewrite orbit_sym H1 s2f eq_sym Eq1.
 move: (SOP group_H to_1 _ H3) => H4; move/isetP:H4=>H4.
 by move: (H4 y); rewrite H1 s2f Eq1.
have C2: forall a, e a -> dvdn p (card (orbit H to a)).
  move => a Ha.
  have F1: (dvdn (card (orbit H to a)) (p ^ n))
    by rewrite -card_H card_orbit_div.
  move/(@dvdn_exp_prime _ _ _ prime_p): F1 => 
      [] [|m] /= H1 H2; last by rewrite H2 dvdn_mulr.
  unfold e in Ha; move/andP: Ha => [_ Ha].
  move/negP: Ha => Ha; case Ha.
  apply/SOP => //. 
  exact: card_orbit1.
move Dn: (n_comp (orbit H to) e) => n1.
elim: n1 e C1 C2 Dn => [|n1 Rec] e C1 C2.
  move/eqP=> Hk0; rewrite -(mod0n p); congr modn.
  apply: (appP set0P eqP) => x; apply/idP=> Hx.
  case/idP: (set0P Hk0 (root (orbit H to) x)); rewrite /setI (roots_root orbit_csym).
  by rewrite -(closed_connect C1 (connect_root _ _)).
case: (pickP (setI (roots (orbit H to)) e));
 last by move => Hk; rewrite /n_comp (eq_card Hk) card0.
move => x Dn.
move: (andP Dn) => [H1 H2].
rewrite /n_comp (cardD1 x) Dn => [] [Dn1].
rewrite -(cardIC (orbit H to x) e).
rewrite -modn_add -(mod0n p) -(add0n 0) -[modn (0 + _) _]modn_add;
  congr modn; congr addn; rewrite mod0n.
  move: (C2 x H2); rewrite /dvdn; move/eqP => H3.
  rewrite -H3; congr modn.
  apply eq_card => z; rewrite /setI.
  case Eq1: (orbit H to x z); last by rewrite andbF.
  rewrite andbT (C1 z x) //  ?H2.
  by rewrite orbit_sym Eq1.
rewrite -{Rec}(Rec (setD e (orbit H to x)));
 first by congr modn; apply: eq_card => y; exact: andbC.
 move=> y z Hyz; rewrite /setD (C1 _ _ Hyz) -!orbit_trans.
 by rewrite (same_connect_r orbit_csym (connect1 Hyz)).
 by move => a; move/andP => [_ Ha]; apply C2.
apply: {n1}etrans Dn1; apply: eq_card => y; rewrite /setD1 /setI andbCA /setD.
rewrite -orbit_trans (sameP (rootP orbit_csym) eqP).
by case Dy: (roots (orbit H to) y) (andP Dn) => //= [] [Dx _]; rewrite (eqP Dy) (eqP Dx).
Qed.

End ModP.

Section PermAction.

Open Scope group_scope.

Variable S : finType.
Let G := perm_finGroupType S.
Variable H : setType G.
Hypothesis group_H: group H.

Definition to (x:S) (u : G) := fun_of_perm u^-1 x.

Lemma to_1 : forall x, to x 1 = x.
Proof.
move => x. rewrite /to; gsimpl.
rewrite /unitg /= /perm_unit /fun_of_perm /=.
by rewrite /comp /perm_of_inj can_fgraph_of_fun /fgraph_of_fun.
Qed.

Lemma to_morph : forall (x y:permType S) z,
  H x -> H y -> to z (x * y) = to (to z x) y.
Proof. 
move => x y z Hx Hy /=.
rewrite /perm_mul /to /=; gsimpl.
rewrite /fun_of_perm /= /comp !can_fgraph_of_fun.
by do 1!rewrite /fun_of_perm /= /comp !can_fgraph_of_fun.
Qed.

End PermAction.

Unset Implicit Arguments.
