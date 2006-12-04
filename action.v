Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
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

Variable (G: finGroupType) (H : seq G).
Hypothesis group_H: group H.
Variable S: finType.

Variable to : G -> fgraphType S S.
Hypothesis to_bij : forall x, H x -> bijective (to x).
Hypothesis to_morph : forall (x y:G) z,
  H x -> H y -> to (x * y) z = to x (to y z).

Lemma to_1: forall x, to 1 x = x.
Proof.
move: (group1 group_H) => H1 x; apply: (bij_inj (to_bij H1)).
by rewrite -to_morph // mul1g.
Qed.

Definition orbit a := maps (fun z => to z a) H.

Lemma orbit_to: forall a x, H x -> orbit a (to x a).
Proof.
by move => a x Hx; rewrite /orbit; apply/mapsP; exists x.
Qed.

Lemma orbit_refl : forall x, orbit x x.
Proof.
move=> x; rewrite /orbit; apply/mapsP. 
exists (Group.unit G); [ exact (group1 group_H) | exact (to_1 x) ].
Qed.

Lemma orbit_sym : forall x y, orbit x y = orbit y x.
Proof.
by move => x y; rewrite /orbit; apply/idP/idP; move/mapsP => [c Hc <-]; 
apply/mapsP; exists (c^-1); rewrite -?to_morph ?mulVg ?to_1 ?groupV.
Qed.

Lemma orbit_trans : forall x y, connect orbit x y = orbit x y.
Proof.
move=> x y; apply/idP/idP; last by move => *; apply connect1.
move/connectP => [p Hp <- {y}].
elim: p x Hp => /= [x _|w p IH x Hp]; first by apply orbit_refl.
move/andP: Hp => [Hw Hp];move/mapsP: Hw => [c Hc Htoc].
have IHw := IH w Hp.
rewrite /orbit in IHw; move/mapsP: IHw => [c1 Hc1 Htoc1].
apply/mapsP; exists (c1*c); last by rewrite to_morph -?Htoc1 -?Htoc.
by apply groupM.
Qed.

Lemma orbit_csym : connect_sym orbit.
Proof. by move=> x y; rewrite !orbit_trans orbit_sym. Qed.

Definition stabilizer a := filter (fun x => to x a == a) H.

Definition SO a := H == stabilizer a.

Lemma eq_filter_sx : 
   forall d,  forall s: seq d, forall f1 f2 : d -> bool,
   (forall a, s a -> f1 a = f2 a) ->
   filter f1 s = filter f2 s.
Proof.
move => d s f1 f2 Hf; elim: s Hf => [|e s1 IH Hf] => //=.
rewrite (Hf e) ?IH // ?mem_adds /setU1; last by apply/orP; left.
move => a Ha; rewrite (Hf a) // ?mem_adds /setU1; last by apply/orP; right.
Qed.

Lemma stabilizerP: forall a x, reflect (to x a = a /\ H x) (stabilizer a x).
Proof.
move => a x; apply: (iffP idP).
by rewrite /stabilizer mem_filter /setI; move/andP => [Htox Hx]; rewrite (eqP Htox);split.
by rewrite /stabilizer mem_filter /setI; move=>[-> Hx]; rewrite eq_refl andTb.
Qed.

Lemma orbitP: forall x a, reflect (exists2 z, H z & to z a = x) (orbit a x).
Proof.
move => x a; apply: (iffP idP).
by rewrite /orbit; move/mapsP=>[c Hc Htoc];exists c.
by move => [c Hc Htoc]; rewrite /orbit; apply/mapsP;exists c.
Qed.

Lemma SOP : forall a, reflect (orbit a =1 set1 a) (SO a).
Proof.
move => a; apply:(iffP eqP).
  move => Hstab x; rewrite /orbit; apply/mapsP.
  case Dx: (a == x);first by exists (Group.unit G); rewrite ?to_1 ?group1 ?(eqP Dx).
  move => [c Hc Htoc]; rewrite Hstab in Hc; move/stabilizerP: Hc => [Htoc' Hx].
  by rewrite Htoc in Htoc'; rewrite Htoc' eq_refl in Dx.
move => Ho. rewrite /stabilizer. 
rewrite (@eq_filter_sx _ _ (fun x => to x a == a) (@setA G)).
  by rewrite filter_setA. 
move => c Hc; change (G c) with true. 
by rewrite eq_sym -(Ho (to c a)); apply/orbitP; exists c.
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

End Action.

Section PermAction.

Open Scope group_scope.

Variable S : finType.
Let G := perm_finGroupType S.
Variable H : seq G.
Hypothesis group_H: group H.

Definition to (u : G) : permType S := u.

Lemma to_bij : forall x:permType S, H x -> bijective (to x).
Proof.
move => x Hx; rewrite /bijective /=.
exists (fun_of_perm (perm_inv (to x))) => y.
  do 1!rewrite /fun_of_perm /= /comp can_graph_of_fun.
  by rewrite finv_f // /to; apply: perm_inj.
do 1!rewrite /fun_of_perm /= /comp can_graph_of_fun.
by rewrite f_finv // /to; apply: perm_inj.
Qed.

Lemma to_morph : forall (x y:permType S) z,
  H x -> H y -> to (x * y) z = to x (to y z).
Proof. 
move => x y z Hx Hy /=.
rewrite /perm_mul /to /=.
by do 1!rewrite /fun_of_perm /= /comp can_graph_of_fun.
Qed.

End PermAction.

