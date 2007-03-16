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

Definition act_fix := stabilizer == H :> setType _.

Lemma act_fixP : reflect (forall x, H x -> to a x = a) act_fix.
Proof.
apply: (iffP eqP). 
  by move/isetP=> Hs x Hx; move/(_ x): Hs; rewrite Hx; case/stabilizerP.
move=> Ha; apply/isetP=> x; move/(_ x): Ha. 
by rewrite s2f; case: (H x) => //= ->; rewrite // set11.
Qed.

Lemma orbit1P : reflect ({:a} = orbit) act_fix.
Proof.
apply: (iffP idP).
  move/act_fixP => Hto; apply/isetP=> x; rewrite s2f.
  apply/eqP/orbitP; last by move=> [z Hz Htoz]; rewrite -(Hto z Hz).
  by move=> <-; exists (1 : G); rewrite ?group1 ?act_1.
move/isetP=> Horb; apply/act_fixP=> x Hx; move/(_ (to a x)): Horb.
by rewrite s2f orbit_to // eq_sym; move/eqP=> ->.
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
Variable A : setType S.




Hypothesis HactsonA : closed (orbit to H) A.

Lemma mpl: modn (card A) p = modn (card (setI (act_fix to H) A)) p.
Proof.
elim: (Datatypes.S _) {-2}(A : set _) (ltnSn (card A)) HactsonA => // m IHm B.
rewrite ltnS => leBm HactB.
case: (pickP (setD B (act_fix to H))) => [a | fixB]; last first.
  congr modn; apply: eq_card => a; rewrite /setI andbC; symmetry.
  move/(_ a): fixB; rewrite /setD andbC; case: (B a) => //=.
  by move/negbEF.
pose C := orbit to H a.
move/andP=> [nfixa Ba]; rewrite -(cardIC C B). 
have [i ->]: exists i, card (setI B C) = (p * p ^ i)%N.
  have ->: card (setI B C) = card C.
    apply: eq_card => b; rewrite /setI andbC; case Cb: (C b) => //=.
    by rewrite -(HactB a).
  have: dvdn (card C) (p ^ n) by rewrite -card_H card_orbit_div.
  case/dvdn_exp_prime=> //= [] [_ fixa|i]; last by exists i.
  case/orbit1P: nfixa; symmetry; exact: card_orbit1.
rewrite mulnC modn_addl_mul {}IHm; last first.
- move=> b1 b2 orbHb12; rewrite /setI (HactB _ b2) //.
  congr andb; congr negb.
  rewrite /C -!orbit_trans in orbHb12 *; apply: same_connect_r => //.
  exact: orbit_csym.
- apply: leq_trans leBm => {m IHm}.
  rewrite -(cardIC C B) -add1n leq_add2r lt0n.
  by apply/set0Pn; exists a; rewrite /setI Ba /C orbit_refl.
congr modn; apply: eq_card => b; rewrite /setI /setC.
case fixb: (act_fix _ H b) => //=; case (B b) => //=.
rewrite /C orbit_sym -(orbit1P _ _ _ fixb).
by apply/iset1P=> Eba; rewrite -Eba fixb in nfixa.
Qed.

End ModP.

Section PermAction.

Open Scope group_scope.

Variable S : finType.
Let G := perm_finGroupType S.

Definition to (x:S) (u : G) := fun_of_perm u x.

Lemma to_1 : forall x, to x 1 = x.
Proof.
move => x; rewrite /to; gsimpl.
rewrite /unitg /= /perm_unit /fun_of_perm /=.
by rewrite /comp /perm_of_inj g2f /fgraph_of_fun.
Qed.

Lemma to_morph : forall (x y:permType S) z,
  to z (x * y) = to (to z x) y.
Proof. 
by move=> *; rewrite /perm_mul /to /fun_of_perm /= /comp !g2f.
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
by rewrite /fun_of_perm g2f.
Qed.

Lemma perm_of_act_morph : forall x y,perm_of_act (x*y) = perm_of_act x * perm_of_act y.
Proof.
move=> x y; apply: eq_fun_of_perm => a.
rewrite {2}/fun_of_perm !g2f /comp !perm_of_op ?groupM //.
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
