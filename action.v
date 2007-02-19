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

Variable (G: finGroupType) (S:finType).

Record action : Type := Action {
  act_f :> S -> G -> S;
  act_1 : forall x, act_f x 1 = x;
  act_morph : forall (x y:G) z, act_f z (x * y) = act_f (act_f z x) y
}.

Variable to : action.

Lemma actK : forall x, cancel (fun e => to e x) (fun e => to e x^-1).
Proof. by move=> x e; rewrite -act_morph ?groupV // mulgV act_1. Qed.

Lemma actKv : forall x, cancel (fun e => to e x^-1) (fun e => to e x).
Proof. move=>x; rewrite -{2}(invgK x); exact:actK. Qed.

Lemma inj_act : forall x, injective (fun e => to e x).
Proof. move=> x; exact: (can_inj (actK x)). Qed.

Variable H : group G.
Variable a : S.

Definition orbit := (fun z => to a z) @: H.

Lemma orbitP: forall x, reflect (exists2 z, H z & to a z = x) (orbit x).
Proof.
by move=> x; apply: (iffP (@iimageP _ _ _ _ _)); case=> y; exists y.
Qed.

Lemma orbit_to: forall x, H x -> orbit (to a x).
Proof. by move=> x Hx; apply/orbitP; exists x. Qed.

Lemma orbit_refl : orbit a.
Proof. rewrite -[a](act_1 to); apply: orbit_to; exact: group1. Qed.

Definition stabilizer := {x, H x && (to a x == a)}.

Lemma stabilizerP: forall x, reflect (H x /\ to a x = a) (stabilizer x).
Proof.
by move=> x; rewrite s2f; apply: (iffP andP) => [] [Hx]; move/eqP.
Qed.

Definition act_fix := H == stabilizer :> setType _.

Lemma act_fixP : reflect (orbit = {:a}) act_fix.
Proof.
apply: (iffP eqP) => [fixH | fix_a]; apply/isetP.
  move=> b; rewrite s2f; apply/idP/eqP=> [|<-]; last exact orbit_refl.
  by case/orbitP=> x; rewrite fixH s2f; case/andP=> _; move/eqP->.
move=>x; rewrite s2f; apply/idP/andP=> [Hx | [] //]; split=> //.
by have:= orbit_to Hx; rewrite fix_a s2f eq_sym.
Qed.


Lemma stab_1: stabilizer 1.
Proof. by apply/stabilizerP; split; [ apply group1 | apply (act_1 to) ]. Qed.

Lemma group_set_stab : group_set stabilizer.
Proof.
apply/groupP; split; first exact: stab_1.
move=> x y; move/stabilizerP => [Hx Htox]; move/stabilizerP => [Hy Htoy].
apply/stabilizerP; split; first by rewrite groupMl.
by rewrite act_morph // Htox // Htoy. 
Qed.

Canonical Structure group_stab := Group group_set_stab.

Lemma subset_stab : subset stabilizer H.
Proof. by apply/subsetP=> x; case/stabilizerP. Qed.

Lemma to_repr_rcoset : forall z, H z -> to a (repr (stabilizer :* z)) = to a z.
Proof.    
move=> z Hz; case: (repr _) / (repr_rcosetP group_stab z) => y.
by move/stabilizerP=> [Hy Dtoy]; rewrite act_morph Dtoy.
Qed.

Lemma card_orbit: card orbit = indexg {stabilizer as group _} H.
Proof.
pose f b := {x, H x && (to a x == b)}.
have injf: injective (fun u : sub_finType orbit => f (val u)).
  move=> [b Hb] [c Hc] /= eq_f; apply: val_inj => /=; apply: eqP.
  case/orbitP: Hb {Hc} => [x Hx Dxa]; move/isetP: eq_f.
  by move/(_ x); rewrite !s2f Dxa Hx eq_refl.
have f_to: forall x, H x -> f (to a x) = stabilizer :* x. 
  move=> x Hx; apply/isetP=> y; have Hx1:= groupVr Hx.
  rewrite !s2f groupMr; case Hy: (H y) => //=.
  by rewrite act_morph (canF_eq (actKv x)).
rewrite /= -card_sub -(card_image injf); apply: eq_card=> A.
apply/imageP/iimageP=> [[[b Hb] _] | [x Hx]] -> {A}/=.
  by case/orbitP: Hb => [x Hx <-]; exists x; rewrite // f_to.
by exists (EqSig orbit _ (orbit_to Hx)); rewrite //= f_to.
Qed.

Lemma card_orbit_div: dvdn (card orbit) (card H).
Proof.
by rewrite -(LaGrange subset_stab) -card_orbit dvdn_mull.
Qed.

Lemma card_orbit1 : card orbit = 1%N -> orbit = {:a}.
Proof.
move=> c1; symmetry; apply/isetP; apply/subset_cardP.
  by rewrite icard1 c1.
by rewrite subset_set1 orbit_refl.
Qed.

End Action.

Section ModP.

Variable (G: finGroupType) (S:finType).


Variable to : action G S.

Variable H : group G. 

(***********************************************************************)
(*                                                                     *)
(*           The mod p lemma                                           *)
(*                                                                     *)
(***********************************************************************) 


Lemma orbit_sym : forall x y, orbit to H x y = orbit to H y x.
Proof.
move=> x y; apply/iimageP/iimageP; case=> z Hz ->;
  exists z^-1; rewrite ?groupV //; symmetry; apply: actK; eauto.
Qed.

Lemma orbit_trans : forall x y, connect (orbit to H) x y = (orbit to H) x y.
Proof.
move=> x y; apply/idP/idP; last by move =>*; apply: connect1.
move/connectP=> [p Hp <- {y}]; rewrite orbit_sym.
elim: p x Hp => [|y p IHp] x /=; first by rewrite orbit_refl.
move/andP=> [Hxy Hp].
move: (IHp _ Hp) => H1. rewrite -/orbit orbit_sym in Hxy.
rewrite orbit_sym /orbit in H1; unlock iimage in H1; rewrite s2f in H1. 
unlock orbit iimage; rewrite s2f -(f_diinv H1).
unlock orbit iimage in Hxy; rewrite s2f in Hxy.
rewrite -(f_diinv Hxy) -{4}(act_1 to y) -(mulgV (diinv H1)).
set k := diinv H1.
set k1 := diinv Hxy.
have F1: H k by apply (a_diinv H1).
have F2: H k1 by apply (a_diinv Hxy).
rewrite act_morph -act_morph.
by apply: image_f_imp; rewrite groupM // groupV.
Qed.

Lemma orbit_csym : connect_sym (orbit to H).
Proof. by move=> x y; rewrite !orbit_trans orbit_sym. Qed.

Variable n p: nat.
Hypothesis prime_p: prime p.
Hypothesis card_H: card H = (p ^ n)%N.

Lemma mpl: modn (card (setA S)) p = modn (card (act_fix to H)) p.
Proof.
rewrite -(addn0 (card (act_fix _ H))) -(cardIC (act_fix to H) (setA S)) /setI.
rewrite -modn_add -[modn (_ + 0) _]modn_add; congr modn; congr addn; rewrite mod0n.
set (e := (fun x : S => (setA S) x && setC (act_fix to H) x)).
have C1: closed (orbit to H) e.
 move => x y; rewrite /e /=.
 case Eq1: (x == y); first by rewrite (eqP Eq1).
 move => H1; apply/negP/negP => H2 H3; case: H2.
   move/act_fixP: H3; move/isetP; move/(_ x).
   by rewrite orbit_sym H1 s2f eq_sym Eq1.
 by move/act_fixP: H3; move/isetP; move/(_ y); rewrite H1 s2f Eq1.
have C2: forall a, e a -> dvdn p (card (orbit to H a)).
  move => a Ha.
  have F1: (dvdn (card (orbit to H a)) (p ^ n))
    by rewrite -card_H card_orbit_div.
  move/(@dvdn_exp_prime _ _ _ prime_p): F1 => 
      [] [|m] /= H1 H2; last by rewrite H2 dvdn_mulr.
  unfold e in Ha; move/andP: Ha => [_ Ha].
  move/negP: Ha => Ha; case Ha.
  apply/act_fixP => //. 
  exact: card_orbit1.
move Dn: (n_comp (orbit to H) e) => n1. 
elim: n1 e C1 C2 Dn => [|n1 Rec] e C1 C2.
  move/eqP=> Hk0; rewrite -(mod0n p); congr modn.
  apply: (appP set0P eqP) => x; apply/idP=> Hx.
  case/idP: (set0P Hk0 (root (orbit to H) x)); rewrite /setI (roots_root orbit_csym).
  by rewrite -(closed_connect C1 (connect_root _ _)).
case: (pickP (setI (roots (orbit to H)) e));
 last by move => Hk; rewrite /n_comp (eq_card Hk) card0.
move => x Dn.
move: (andP Dn) => [H1 H2].
rewrite /n_comp (cardD1 x) Dn => [] [Dn1].
rewrite -(cardIC (orbit to H x) e).
rewrite -modn_add -(mod0n p) -(add0n 0) -[modn (0 + _) _]modn_add;
  congr modn; congr addn; rewrite mod0n.
  move: (C2 x H2); rewrite /dvdn; move/eqP => H3.
  rewrite -H3; congr modn.
  apply eq_card => z; rewrite /setI.
  case Eq1: (orbit to H x z); last by rewrite andbF.
  rewrite andbT (C1 z x) //  ?H2.
  by rewrite orbit_sym Eq1.
rewrite -{Rec}(Rec (setD e (orbit to H x)));
 first by congr modn; apply: eq_card => y; exact: andbC.
 move=> y z Hyz; rewrite /setD (C1 _ _ Hyz) -!orbit_trans.
 by rewrite (same_connect_r orbit_csym (connect1 Hyz)).
 by move => a; move/andP => [_ Ha]; apply C2.
apply: {n1}etrans Dn1; apply: eq_card => y; rewrite /setD1 /setI andbCA /setD.
rewrite -orbit_trans (sameP (rootP orbit_csym) eqP).
by case Dy: (roots (orbit to H) y) (andP Dn) => //= [] [Dx _]; rewrite (eqP Dy) (eqP Dx).
Qed.

End ModP.

Section PermAction.

Open Scope group_scope.

Variable S : finType.
Let G := perm_finGroupType S.

Definition to (x:S) (u : G) := fun_of_perm u x.

Lemma to_1 : forall x, to x 1 = x.
Proof.
move => x. rewrite /to; gsimpl.
rewrite /unitg /= /perm_unit /fun_of_perm /=.
by rewrite /comp /perm_of_inj can_fgraph_of_fun /fgraph_of_fun.
Qed.

Lemma to_morph : forall (x y:permType S) z,
  to z (x * y) = to (to z x) y.
Proof. 
by move=> *; rewrite /perm_mul /to /fun_of_perm /= /comp !can_fgraph_of_fun.
Qed.

Definition perm_act := Action to_1 to_morph.

End PermAction.

Require Import normal.

Section PermFact.

Variable S :finType.
Variable G :finGroupType.
Variable to : action G S.

Definition perm_of_act x := perm_of_inj (@inj_act _ _ to x).

Lemma perm_of_op : forall x a, perm_of_act x a = to a x.
Proof.
move=> x a; rewrite /perm_of_act.
by rewrite /fun_of_perm can_fgraph_of_fun.
Qed.

Lemma perm_of_act_morph : forall x y,perm_of_act (x*y) = perm_of_act x * perm_of_act y.
Proof.
move=> x y; apply: eq_fun_of_perm => a.
rewrite {2}/fun_of_perm !can_fgraph_of_fun /comp !perm_of_op ?groupM //.
by rewrite act_morph.
Qed.


Canonical Structure perm_of_op_action := perm_act S.

Lemma act_perm_of_act : forall x a,
   act_f perm_of_op_action a (perm_of_act x) = to a x.
Proof. exact: perm_of_op. Qed.


End PermFact. 

(*
Section Try.

Variable S : finType.
Variable G : finGroupType.
Variable H : setType G.
Hypothesis gH : group H.

Record action_op : Type := ActionOp {
  actop_f :> S -> G -> S;
  actop_1 : forall x, actop_f x 1 = x;
  actop_morph : forall (x y:G) z, H x -> H -> actop_f z (x * y) = actop_f (actop_f z x) y
}.
*)
