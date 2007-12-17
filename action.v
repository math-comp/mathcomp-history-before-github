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
Require Import tuple.
Require Import normal.

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

Section Def.

Variable H : setType G.
Variable a : S.

Definition transitive (S1: set S) := 
  forall x: S, S1 x -> (to x) @: H =1 S1.

Definition orbit := (fun z => to a z) @: H.

Lemma orbitP: forall x, reflect (exists2 z, H z & to a z = x) (orbit x).
Proof.
by move=> x; apply: (iffP (@iimageP _ _ _ _ _)); case=> y; exists y.
Qed.

Lemma orbit_to: forall x, H x -> orbit (to a x).
Proof. by move=> x Hx; apply/orbitP; exists x. Qed.

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

Lemma subset_stab : subset stabilizer H.
Proof. by apply/subsetP=> x; case/stabilizerP. Qed.

Lemma trans_orbit: forall S1: set S, 
  S1 a -> transitive S1 -> orbit =1 S1.
Proof.
move => S1 Ha Ht z.
rewrite -(Ht _ Ha) /orbit.
by apply/iimageP/iimageP.
Qed.

End Def.

Variable H : group G.
Variable a : S.

Lemma orbit_refl : orbit H a a.
Proof. rewrite -{2}[a](act_1 to); apply: orbit_to; exact: group1. Qed.

Lemma orbit1P : reflect ({:a} = orbit H a) (act_fix H a).
Proof.
apply: (iffP idP).
  move/act_fixP => Hto; apply/isetP=> x; rewrite s2f.
  apply/eqP/orbitP; last by move=> [z Hz Htoz]; rewrite -(Hto z Hz).
  by move=> <-; exists (1 : G); rewrite ?group1 ?act_1.
move/isetP=> Horb; apply/act_fixP=> x Hx; move/(_ (to a x)): Horb.
by rewrite s2f orbit_to // eq_sym; move/eqP=> ->.
Qed.

Lemma stab_1: stabilizer H a 1.
Proof. by apply/stabilizerP; split; [ apply group1 | apply (act_1 to) ]. Qed.

Lemma group_set_stab : group_set (stabilizer H a).
Proof.
apply/groupP; split; first exact: stab_1.
move=> x y; move/stabilizerP => [Hx Htox]; move/stabilizerP => [Hy Htoy].
apply/stabilizerP; split; first by rewrite groupMl.
by rewrite act_morph // Htox // Htoy. 
Qed.

Canonical Structure group_stab := Group group_set_stab.


Lemma to_repr_rcoset : forall z, H z -> to a (repr (stabilizer H a :* z)) = to a z.
Proof.    
move=> z Hz; case: (repr _) / (repr_rcosetP group_stab z) => y.
by move/stabilizerP=> [Hy Dtoy]; rewrite act_morph Dtoy.
Qed.

Lemma card_orbit: card (orbit H a) = indexg {stabilizer H a as group _} H.
Proof.
pose f b := {x, H x && (to a x == b)}.
have injf: injective (fun u : sub_finType (orbit H a) => f (val u)).
  move=> [b Hb] [c Hc] /= eq_f; apply: val_inj => /=; apply: eqP.
  case/orbitP: Hb {Hc} => [x Hx Dxa]; move/isetP: eq_f.
  by move/(_ x); rewrite !s2f Dxa Hx eq_refl.
have f_to: forall x, H x -> f (to a x) = stabilizer H a :* x. 
  move=> x Hx; apply/isetP=> y; have Hx1:= groupVr Hx.
  rewrite !s2f groupMr; case Hy: (H y) => //=.
  by rewrite act_morph (canF_eq (actKv x)).
rewrite /= -card_sub -(card_image injf); apply: eq_card=> A.
apply/imageP/iimageP=> [[[b Hb] _] | [x Hx]] -> {A}/=.
  by case/orbitP: Hb => [x Hx <-]; exists x; rewrite // f_to.
by exists (EqSig (orbit H a) _ (orbit_to a Hx)); rewrite //= f_to.
Qed.

Lemma card_orbit_div: dvdn (card (orbit H a)) (card H).
Proof.
by rewrite -(LaGrange (subset_stab _ _)) -card_orbit dvdn_mull.
Qed.

Lemma card_orbit1 : card (orbit H a) = 1%N -> orbit H a = {:a}.
Proof.
move=> c1; symmetry; apply/isetP; apply/subset_cardP.
  by rewrite icard1 c1.
by rewrite subset_set1 orbit_refl.
Qed.

Lemma trans_div: forall S1: set S, S1 a -> 
  transitive H S1 -> dvdn (card S1) (card H).
Proof.
move => S1 Ha Ht.
suff ->: card S1 = card (orbit H a) by apply: card_orbit_div.
by apply: sym_equal; apply: eq_card; apply: trans_orbit.
Qed.

End Action.

Section Faithful.

Variable S :finType.
Variable G :finGroupType.
Variable to : action G S.

Section Def.

Variable H : setType G. 
Variable S1: set S.

Definition akernel := setnI S1 (stabilizer to H).

Lemma akernelP: forall x,
  reflect (forall y, S1 y -> H x /\ to y x = y) (akernel x).
Proof.
move=> x; apply: (iffP idP).
  move/setnIP => HH y Hy; move: (HH y Hy) => /=.
  by rewrite s2f; case/andP => H1; case/eqP; split.
move=> HH; apply/setnIP => y Hy.
by rewrite s2f; case: (HH _ Hy) => -> ->; rewrite eq_refl.
Qed.


Definition faithful := card akernel == 1%nat.

End Def.

Variable H: group G.
Variable S1: set S.

Lemma akernel1: akernel H S1 1.
Proof.
by apply/akernelP => y Hy; rewrite act_1; split.
Qed.

Lemma faithfulP:
  reflect (forall x, (forall y, S1 y -> H x /\ to y x = y) -> x = 1) 
          (faithful H S1).
Proof.
apply: (iffP idP).
  move=> HH x Hi.
  have F1: akernel H S1 x by apply/akernelP => y Hy; case: (Hi _ Hy) => *; split.
  apply: sym_equal; apply/eqP.
  move: HH; rewrite /faithful (cardD1 1) akernel1 (cardD1 x) /setD1 F1.
  by case: (1 == x).
move=> HH.
case E1: (set0b (setD1 (akernel H S1) 1)).
  rewrite /set0b in E1.
  by rewrite /faithful (cardD1 1) akernel1 (eqP E1).
case/set0Pn: E1 => x; case/andP => Hx; move/akernelP => Hx1.
case/negP: Hx; apply/eqP; apply: sym_equal.
by apply: HH.
Qed.  

End Faithful.

Section FaithfulProp.

Variable S :finType.
Variable G :finGroupType.
Variable to : action G S.
Variable K H : group G. 
Variable S1: set S.
Variable SubKH: subset K H.

Lemma subset_faithful: faithful to H S1 -> faithful to K S1.
Proof.
move/faithfulP => HH.
apply/faithfulP => x HH1; apply: HH.
move=> y Hy; case: (HH1 _ Hy) => HH2 HH3.
by split; first by apply: (subsetP SubKH).
Qed.

End FaithfulProp.


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

Lemma perm_act1P: forall d (x: permType d),  reflect  (forall y, perm_act  d y  x  =  y)  (x == 1).
move=> d x ;apply:(iffP idP); first by move/eqP=> -> y;apply:act_1.
move=> H;apply/eqP;apply:eq_fun_of_perm.
by move => z; move:(H z); rewrite perm1.
Qed.


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

Section Primitive.

Variable (G: finGroupType) (S:finType).

Variable to : action G S.
Variable H : group G.
Variable S1: set S.

Definition primitive :=
  forallb P :  fgraphType S (fgraph_eqType S bool_finType),
  (forallb x: S, S1 x ==> P x x) &&
  (forallb x: S, forallb y: S, forallb g: G,
     [==> S1 x, S1 y, H g, P x y => P (to x g) == P (to y g)])
   ==> (forallb x : S, forallb y : S, [==> S1 x, S1 y, P x y => x == y]) 
     ||  
       (forallb x : S, forallb y : S, [==> S1 x, S1 y => P x y]).

Lemma primitiveP:
  reflect 
  (forall (P: S -> set S),
   (forall x, S1 x -> P x x) ->
   (forall x y g, S1 x -> S1 y -> H g -> P x y -> P (to x g) =1 P (to y g)) ->
   (forall x y, S1 x -> S1 y -> P x y -> x = y) 
   \/
   (forall x y, S1 x -> S1 y -> P x y))
   primitive.
Proof.
apply: (iffP idP).
  move => Hpr P Hr Ht. 
  move/forallP: Hpr.
  pose fP := fgraph_of_fun (fun x: S => (fgraph_of_fun (P  x))).
  move /(_ fP); move/implyP => Hf.
  set F := _ || _ in Hf.
  have F1: F; rewrite /F.
    apply: Hf; apply/andP; split.
      by apply/forallP => x; apply/implyP; rewrite /fP !g2f; exact: Hr.
    apply/forallP => x; apply/forallP => y; apply/forallP => g.
    rewrite /fP !g2f.
    apply/implyP => Hx; apply/implyP => Hy; apply/implyP => Hg; apply/implyP => Hf. 
    by apply/eqP; apply/fgraphP => z; rewrite !g2f; apply: Ht.
  case/orP: F1; move/forallP => Hc; [left | right].
    move=> x y Hx1 Hx2 Hp.
    move/forallP: (Hc x); move/(_ y); move/implyP; move/(_ Hx1).
    move/implyP; move/(_ Hx2); rewrite /fP !g2f; move/implyP; move/(_ Hp).
    by move => HH; apply/eqP.
  move=> x y Hx1 Hx2.
  move/forallP: (Hc x); move/(_ y); move/implyP; move/(_ Hx1).
  by move/implyP; move/(_ Hx2); rewrite /fP !g2f.
move=> Hf; apply/forallP => P; apply/implyP; case/andP => Hr Hf1.
case (Hf (fun x => fun_of_fgraph (P x))).
- by move=> x Hx; move/forallP: Hr; move/(_ x); move/implyP => HH; exact: HH.
- move=> x y g Hx Hy Hg Hp; move/forallP: Hf1; move/(_ x);
    move/forallP; move/(_ y); move/forallP; move/(_ g);
    move/implyP; move/(_ Hx); move/implyP; move/(_ Hy); move/implyP; move/(_ Hg).
    by move/implyP; move/(_ Hp); move/eqP; move/fgraphP.
- move=> Hi; apply/orP; left; apply/forallP => x; apply/forallP => y.
  apply/implyP => Hx; apply/implyP => Hy; apply/implyP => Hp.
  by apply/eqP; apply Hi.
move=> Hi; apply/orP; right; apply/forallP => x; apply/forallP => y.
by apply/implyP => Hx; apply/implyP => Hy; apply: Hi.
Qed.

Hypothesis Htrans: transitive to H S1.

Lemma primitivePt: 
  reflect 
  (forall Y,
    subset Y S1 ->
    wdisjointn H (fun z => (image (fun t => to t z) Y)) ->
    card Y <= 1 \/ Y =1 S1)
   primitive.
Proof.
have FF0: forall x g, S1 x -> H g -> S1 (to x g).
  by move => x g Sx Hg; rewrite -(Htrans Sx); apply/iimageP; exists g.
apply: (iffP idP).
  move=> Hp Y HY Hd.
  case E1: (_ <= _); first by left.
  right; move/idP: E1; move/idP; rewrite -(ltnNge) => E1.
  have F1: ~Y =1 set0 by move => F1; move: E1; rewrite (eq_card F1) card0.
  move/set0P: F1; case/set0Pn => x Hx.
  have S1x: S1 x by apply: (subsetP HY).
  pose g_rep := fun z =>
    (if pick (setI H (preimage (to x) (set1 z))) is (Some a)
     then a else 1).
  have Hg_rep1: forall z, H (g_rep z).
    rewrite /g_rep => z1; case: (pickP _).
      by move=> x1; case/andP.
    by move=> _; apply: group1.
  have Hg_rep: forall z, S1 z -> to x (g_rep z) = z.
    move=> z; rewrite -(Htrans S1x).
    case/iimageP => z1 Hz1 Hz2.
      rewrite /g_rep; case: (pickP _).
      by move=> x1; case/andP => _; move/eqP.
    move/(_ z1); rewrite /setI Hz1 /=.
    by rewrite /preimage Hz2 eq_refl.
  pose YY := fun k => image (fun z => to z k) Y.
  move/primitiveP: Hp; move/(_ (fun z => YY (g_rep z))).
  case.
  - by move=> x1 Hx1; apply/imageP; exists x => //; rewrite Hg_rep.
  - have FF: forall (x1: S) (g : G),
     S1 x1 -> H g ->  YY (g_rep (to x1 g)) =1 YY (g_rep x1 * g).
      move=> x1 g Hx1 Hg.
      apply: (Hd _ _ (to x1 g)) => //; first by apply: groupM.
      apply/imageP; exists x => //; rewrite Hg_rep //; first by exact: FF0.
      by apply/imageP; exists x => //; rewrite act_morph Hg_rep.
    move=> x1 y1 g Hx1 Hy1 Hg HH z.
      rewrite FF // FF //; apply: (Hd _ _ (to y1 g)) => //; try exact: groupM.
      case/imageP: HH => z2 Hz2 ->.
      by apply/imageP; exists z2 => //; rewrite act_morph.
    by apply/imageP; exists x => //; rewrite act_morph Hg_rep.
  - have F1: ~(setD1 Y x) =1 set0.
      by move=> F1; move: E1; rewrite (cardD1 x) Hx (eq_card F1) card0.
    move/set0P: F1; case/set0Pn => z; case/andP => Hz Hz1 HH.
    case/negP: Hz; apply/eqP; apply: HH => //.
      by apply: (subsetP HY).
    have <-: YY 1 =1 YY (g_rep x).
      apply: (Hd _ _ x) => //.
        by apply/imageP; exists x => //; rewrite act_1.
      by apply/imageP; exists x => //; rewrite Hg_rep.
    by apply/imageP; exists z => //; rewrite act_1.
  move => HH y.
  apply/idP/idP => S1y; first by apply: (subsetP HY).
  have <-: YY 1 =1 Y.
    move => z; apply/imageP/idP; first by case => u Hu ->; rewrite act_1.
    by move => Hz; exists z => //; rewrite act_1.
  suff ->: YY 1 =1 YY (g_rep x) by apply: HH.
  apply: (Hd _ _ x) => //; first by apply/imageP; exists x => //; rewrite act_1.
  by apply/imageP; exists x => //; rewrite Hg_rep.
move=> HY; apply/primitiveP => P Hp1 Hp2.
case E1: (set0b S1); first by left => x; move/set0P: E1 => ->.
case/set0Pn: E1 => z Sz.
pose Y := (setI S1 (P z)).
pose YY := fun k => image (fun z => to z k) Y.
have FF: forall g, H g -> YY g =1 setI S1 (P (to z g)).
  move=> g Hg z1.
  apply/imageP/andP.
    case => x1; case/andP => Hx1 Hx2 ->.
    have F1: (S1 (to x1 g)) by exact: FF0.
    by split => //; rewrite (Hp2 z x1 g) // Hp1.
  case=> Hx1 Hx2; exists (to z1 g^-1); last by rewrite -act_morph mulVg act_1.
  apply/andP.
  have F1: (S1 (to z1 g^-1)) by apply: FF0; rewrite // groupV.
  split => //.
  by move: (Hp2 (to z g) z1 g^-1); rewrite -act_morph mulgV act_1 => -> //;
    [rewrite Hp1 | apply: FF0 | rewrite groupV].
case: (HY Y) => //; first by apply/subsetP => y Hy; case/andP: Hy.
- move=> g1 g2 x1 Hg1 Hg2; rewrite -/YY !FF //.
  case/andP => Hs1 HP1; case/andP => Hs2 HP2 z1.
  rewrite !FF //.
  have F1: P (to (to z g1) 1) =1 P (to x1 1) by apply: Hp2 => //; exact: FF0.
  have F2: P (to (to z g2) 1) =1 P (to x1 1) by apply: Hp2 => //; exact: FF0.
  by rewrite !act_1 in F1 F2; rewrite /setI F1 F2.
- move=> HH.
  have F0: Y z by rewrite /Y /setI Sz Hp1.
  have F1: Y =1 set1 z.
    move => x; case E1: (z == x); first by move/eqP: E1 => <-.
    apply/negP => E2.
    have F1: (setD1 Y z) x by rewrite /setD1 E2 andbT; move/negP: E1; move/negPn.
    by move: HH; rewrite (cardD1 z) F0; rewrite (cardD1 x) F1.
  left => x1 y1 S1x1 S1y1 HP.
  move: (S1x1); rewrite -(Htrans Sz); case/iimageP => g Hg Hg1.
  apply: (@inj_act _ _ to g^-1).
  rewrite Hg1 -act_morph mulgV act_1.
  apply/eqP; rewrite <- F1.
  have F2: P (to (to z g) g^-1) =1 P (to y1 g^-1) by
    apply: Hp2 => //; [exact: FF0 | rewrite groupV | rewrite <- Hg1].
  rewrite -act_morph mulgV act_1 in F2.
  by rewrite /Y /setI F2 Hp1 // ?andbT; apply: FF0; rewrite // groupV.
move=> HH; right => x1 y1 S1x1 S1y1.
move: (S1x1); rewrite -(Htrans Sz); case/iimageP => g Hg Hg1.
rewrite Hg1.
have F1: S1 (to y1 g^-1) by apply: FF0; rewrite // groupV.
have ->: y1 = to (to y1 g^-1) g by rewrite -act_morph mulVg act_1.
rewrite (Hp2 z (to y1 g^-1) g) // ?Hp1 //.
  by apply: FF0; rewrite // groupV.
by rewrite -HH in F1; case/andP: F1.
Qed.

Lemma prim_trans_norm: forall K: group G, primitive -> subset K H ->
   K <| H -> subset K (akernel to H S1) \/ transitive to K S1.
Proof.
move=> K Hp Hs Hn.
set P := fun x => image (to x) K.
move/primitiveP: Hp; move/(_ P); case.
- move=> x Hx; apply/imageP; exists (1: G); first by apply: group1.
  by rewrite act_1.
- move=> x y g Hx Hy Hg; case/imageP => g1 Kg1 Heg1 z.
  apply/imageP/imageP; case => g2 Kg2 Heg2.
    exists (g^-1 * g1^-1 * g * g2); last first.
      by rewrite Heg2 Heg1 -!act_morph; congr (to x); gsimpl.
    apply: groupM => //; move/normalP: Hn => Hn1.
    by rewrite -(Hn1 g) // s2f /conjg; gsimpl; rewrite groupV.
  exists (g^-1 * g1 * g * g2); last first.
    by rewrite Heg2 Heg1 -!act_morph; congr (to x); gsimpl.
  apply: groupM => //; move/normalP: Hn => Hn1.
  by rewrite -(Hn1 g) // s2f /conjg; gsimpl; rewrite groupV.
- move=> HH; left; apply/subsetP => x Kx.
  have Hx: H x by apply: (subsetP Hs).
  apply/akernelP => y Hy; split => //.
  apply: HH => //; first by rewrite -(Htrans Hy); apply/iimageP; exists x.
 apply/imageP; exists x^-1; first by rewrite groupV.
 by rewrite -act_morph mulgV act_1.
move=> HH; right => x Hx y.
apply/iimageP/idP.
  case=> g Kg ->; rewrite -(Htrans Hx); apply/iimageP; exists g =>//.
  by apply: (subsetP Hs).
by move=> Hy; case/imageP: (HH _ _ Hx Hy) => g Kg ->; exists g.
Qed.

End Primitive.

Section NTransitive.

Variable (G: finGroupType) (S:finType).

Variable to : action G S.
Variable H : group G.
Variable S1: set S.
Variable n: nat.

Definition distinctb (x: tuple_finType S n) := 
  uniq (fval x).
Definition dtuple := 
  @sub_finType (tuple_finType S n) distinctb.

Let f_aux1 x a: size x = 
 card (setA I_(n))
  ->size (maps (fun z : S => to z a) x) = card (setA I_(n)).
move => x a Hx.
by rewrite -Hx size_maps.
Qed.

Definition f_naction (x:dtuple) (a: G):=
match x with
| EqSig tx x =>
    match tx as f return (distinctb f -> dtuple) with
    | Fgraph x Hx =>
        fun Dx  =>
        EqSig distinctb
          (Fgraph (f_aux1 a Hx))
          (eq_ind_r (fun x : bool => x) Dx
             (uniq_maps (inj_act (x:=a)) x))
    end x
end.

Definition naction: action G dtuple.
exists f_naction.
  move => [[x Hx] Dx].
  rewrite /f_naction; apply/val_eqP => /=.
  rewrite /set1 /=; apply/eqseqP.
  rewrite -{2}(maps_id x); apply: eq_maps => y.
  by exact: act_1.
move=> x y [[z Hz] Dz].
rewrite /f_naction; apply/val_eqP => /=.
rewrite /set1 /=; apply/eqseqP.
by rewrite -maps_comp; apply: eq_maps => t; exact: act_morph.
Defined.

Definition dlift: (set dtuple) := fun x =>
match x with
| EqSig (Fgraph x _) _ => all S1 x
end.

Definition ntransitive := 
   transitive naction H dlift /\ n <= card S1.

End NTransitive.

Section NTransitveProp.

Lemma dliftA: forall (S: finType) n (x: dtuple S n), 
   dlift (setA S) x.
Proof.
by move=> S n [[x Hx] Dx]; apply/allP.
Qed.

Lemma dlift_sub_set:
forall m (S: finType) (S1 S2: set S),
 sub_set S1 S2 -> sub_set (dlift (n := m) S1) (dlift (n := m) S2).
Proof.
move=> m S S1 S2 H [[x Hx] Hx1] /= H1.
apply/allP => z Hz.
apply: (H z).
by apply: (allP H1 z).
Qed.

Lemma dlift_eq: forall m (S: finType) (S1 S2: set S)
                        (t: dtuple S m),
  S1 =1 S2 -> (dlift S1 t) = dlift S2 t.
Proof.
by move=> m S S1 S2 t H; apply/idP/idP => H1;
  apply: dlift_sub_set H1; move => z; rewrite H.
Qed.

Definition dtuple_get (S: finType) m (t: dtuple S m) := 
match t with
| EqSig (Fgraph x1 _) _ => x1
end.

Definition dtuple_in (S: finType) m (x: S) (t: dtuple S m) := 
 dtuple_get t x.

Lemma dtuple_get_size (S: finType) m (t: dtuple S m): 
 size (dtuple_get t) = m.
Proof.
move=> S m [[x Hx] Dx] /=.
by move: (Hx); rewrite card_ordinal.
Qed.

Lemma dtuple_get_card (S: finType) m (t: dtuple S m): 
 card (dtuple_get t) = m.
Proof.
move=> S m [[x Hx] Dx] /=.
move: (Hx); rewrite card_ordinal.
by move => <-; apply/card_uniqP.
Qed.

Lemma dtuple_get_sub_set (S: finType) (S1: set S) m (t: dtuple S m): 
 dlift S1 t -> sub_set (dtuple_get t) S1.
Proof.
move=> S S1 m [[x Hx] Dx] /= H1 x1 Hx1.
exact: (allP H1).
Qed.

Let dtuple_add_aux: forall m (S: finType) x (x1: seq S),
  size x1 = card (setA I_(m)) ->
  size (Adds x x1) = card (setA I_(m + 1)).
move=> m S x x1 Hx1.
by rewrite card_ordinal addnC -(card_ordinal m) -Hx1.
Qed.

Definition dtuple_add (S: finType) m (x:S) (t: dtuple S m):
    ~~(dtuple_in x t) -> dtuple S (m + 1).
move => S m x [[x1 Hx1] Dx1] /= H.
exists (Fgraph (dtuple_add_aux x Hx1)).
by rewrite /distinctb /= H.
Defined.

Definition dtuple_hd S m s (t: dtuple S m) := head s (dtuple_get t).

Lemma dtuple_hd_add (S: finType) m (x y:S) (t: dtuple S m) 
         (F: ~~(dtuple_in x t)):
  dtuple_hd y (dtuple_add F) = x.
Proof.
by move=> S m x y [[xx Hxx] Dx].
Qed.

Let dtuple_tl_aux: forall m (S: finType) (x1: seq S),
  size x1 = card (setA I_(m + 1)) ->
  size (behead x1) = card (setA I_(m)).
move=> m S [| x1 l] /=.
  by rewrite card_ordinal addnC.
rewrite !card_ordinal addn1; move/eqP.
by rewrite eqSS; move/eqP.
Qed.

Definition dtuple_tl S m (t: dtuple S (m + 1)): dtuple S m.
 move => S m [[x Hx] Dx].
exists (Fgraph (dtuple_tl_aux Hx)).
case: (x) Hx Dx; rewrite /distinctb //= => a l _.
by case/andP.
Defined.

Lemma dtuple_tl_add (S: finType) m (x:S) (t: dtuple S m) 
         (F: ~~(dtuple_in x t)):
  dtuple_tl (dtuple_add F) = t.
Proof.
move=> S m x [[xx Hxx] Dx] F; apply/val_eqP.
by rewrite /set1 /=.
Qed.

Lemma dtuple_hd_tl (S: finType) m (x:S) (t1 t2: dtuple S (m + 1)):
  dtuple_hd x t1 = dtuple_hd x t2 ->
  dtuple_tl t1 = dtuple_tl t2 ->
  t1 = t2.
Proof.
move=> S m x [[[|t1 l1] Ht1] Dt1].
  by apply False_ind; move: (Ht1); rewrite /= card_ordinal addnC.
move=> [[[|t2 l2] Ht2] Dt2].
  by apply False_ind; move: (Ht2); rewrite /= card_ordinal addnC.
rewrite /dtuple_hd /= => H1.
move/val_eqP; rewrite /set1 /= => H2.
by apply/val_eqP; rewrite /set1 /= /set1 /= H1 eqseqE H2 eq_refl.
Qed.

Lemma dlift_add:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S m)
(F1 : ~~ dtuple_in a1 x),
 dlift S1 x -> S1 a1 -> dlift S1 (dtuple_add F1).
Proof.
by move => m S S1 a1 [[x Hx] Dx] /= _ -> ->.
Qed.

Lemma dlift_addI:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S m)
(F1 : ~~ dtuple_in a1 x),
dlift S1 (dtuple_add F1) -> dlift S1 x.
Proof.
move => m S S1 a1 [[x Hx] Dx] /=; case (all S1 x) => //.
by rewrite andbF.
Qed.

Lemma dlift_hd:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S (m + 1)),
 dlift S1 x ->
 S1 (dtuple_hd a1 x).
Proof.
move => m S S1 a1 [[[| x l] Hx] Dx]; last by case/andP.
by apply False_ind; move: (Hx); rewrite card_ordinal addnC.
Qed.

Lemma dlift_tl:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S (m + 1)),
 dlift S1 x ->
 dlift (setD1 S1 (dtuple_hd a1 x)) (dtuple_tl x).
Proof.
move=> m S S1 a1 [[[| x l] Hx] Dx] //.
rewrite /dlift /dtuple_tl /dtuple_hd.
move: Dx; rewrite /distinctb /=; case/andP => Dx Dx1.
case/andP => Dx2; move/allP => Dx3.
apply/allP => z Hz.
rewrite /setD1 Dx3 ?Hz // andbT.
elim: (l) Dx Dx1 Hz => //= a l1 Hrec Hn1; move/andP => [Hn2 Hu].
case/orP => [| HH].
  move/eqP => <-; apply/negP => HH; case/negP: Hn1.
  by rewrite (eqP HH) setU11.
apply: Hrec => //; apply/negP => HH1; case/negP: Hn1.
by rewrite/setU1 HH1 orbT.
Qed.

Lemma dlift_tlw:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S (m + 1)),
 dlift S1 x -> dlift S1 (dtuple_tl x).
Proof.
move=> m S S1 a1 x H.
have F := dlift_tl a1 H.
by apply: dlift_sub_set F => z; case/andP.
Qed.

Lemma dlift_add_gen:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S m)
(F1 : ~~ dtuple_in a1 x),
 dlift S1 x -> dlift (setU1 a1 S1) (dtuple_add F1).
Proof.
move=> m S S1 a1 [[x Hx] Dx] /=.
rewrite setU11 /= => H.
move/allP => H1; apply/allP => xx Hxx.
by rewrite /setU1 H1 // orbT.
Qed.

Lemma naction_hd:
forall m (G: finGroupType) 
  (S: finType) a (a1: S) (to: action G S) (x: dtuple S m),
 0 < m -> dtuple_hd a1 (naction to m x a) = to (dtuple_hd a1 x) a.
Proof.
move=> m G S a a1 xto [[[|x l] Hx] Dx]; rewrite /dtuple_hd //.
by move: (Hx); rewrite /= card_ordinal /= => <-.
Qed.

Lemma naction_tl:
forall m (G: finGroupType)
  (S: finType) a (to: action G S) (x: dtuple S (m + 1)),
 dtuple_tl (naction to (m + 1) x a) = naction to m (dtuple_tl x) a.
Proof.
move=> m G S a xto [[x Hx] Dx]; rewrite /dtuple_tl //.
apply/val_eqP; rewrite /set1 /=.
by case: (x) (Hx); rewrite card_ordinal.
Qed.

Variable (G: finGroupType) (S:finType).
Variable to : action G S.
Variable H : group G.
Variable S1: set S.


Lemma ntransitive0: ntransitive to H S1 0.
Proof.
split => //.
rewrite /transitive /dtuple => x Hx y.
apply/idP/idP => H1; first by case: (y) => [[[|yy ll] Hyy] Dyy].
apply/iimageP; exists (1:G) => //.
case: (x) => [[[|xx ll] Hxx]  Dxx] => //.
case: (y) => [[[|yy ll] Hyy] Dyy] => //.
by apply/val_eqP.
Qed.

Lemma ntransitive_weak: forall k m,
k <= m -> ntransitive to H S1 m-> ntransitive to H S1 k.
Proof.
assert (F: forall m, ntransitive to H S1 (m + 1) -> ntransitive to H S1 m).
  move=> m [Ht Hc]; split; rewrite addnC in Hc; last first.
    by apply: leq_trans Hc; rewrite leqnSn.
  move=> x Hx y.
  pose x1 := dtuple_get x.
  have F: ~~ set0b  (setI S1 (setC x1)).
    rewrite /set0b; apply/negP => HH.
    move: Hc; rewrite -(cardIC x1) (eqP HH) addn0.
    suff ->: card (setI S1 x1) = card x1 by rewrite /x1 dtuple_get_card add1n ltnn.
    apply: eq_card => z; rewrite /setI.
    move: (@dtuple_get_sub_set S S1 m x Hx z).
    by rewrite -/x1; case (x1 z); case (S1 z) => // ->.
  case/set0Pn: F => a1; case/andP => Ha1 Hb1.
  have F1: ~~ dtuple_in a1 x by done.
  pose x2 := dtuple_add F1; pose y1 := dtuple_get y.
  apply/idP/idP => Hy; last first.
    have F: ~~ set0b  (setI S1 (setC y1)).
      rewrite /set0b; apply/negP => HH.
      move: Hc; rewrite -(cardIC y1) (eqP HH) addn0.
      suff ->: card (setI S1 y1) = card y1
        by rewrite /x1 dtuple_get_card add1n ltnn.
      apply: eq_card => z; rewrite /setI.
      move: (@dtuple_get_sub_set S S1 m y Hy z).
      by rewrite -/y1; case (y1 z); case (S1 z) => // ->.
    case/set0Pn: F => a2; case/andP => Ha2 Hb2.
    have F2: ~~ dtuple_in a2 y.
      move: Hb2; rewrite /y1.
      by case: (y) => [[yy Hyy] Dyy].
    pose y2 := dtuple_add F2.
    have DLx2: dlift S1 x2 by apply: dlift_add.
    have DLy2: dlift S1 y2 by apply: dlift_add.
    move: (Ht _ DLx2 y2); rewrite DLy2.
    move/iimageP => [a Ha] Ha'.
    apply/iimageP; exists a => //.
    rewrite /y2 /x2 in Ha'.
    by rewrite -(dtuple_tl_add F2) Ha' naction_tl dtuple_tl_add.
  case/iimageP: Hy => a Ha Hya.
  have DLx2: dlift S1 x2 by rewrite /x2; apply dlift_add.
  pose z := naction to (m + 1) x2 a.
  have ->: y = dtuple_tl z by rewrite /z Hya /x2 naction_tl dtuple_tl_add.
  apply: dlift_tlw => //; rewrite /z -(Ht x2) //.
  by apply/iimageP; exists a.
move=> k m Hm Ht; rewrite -(leq_sub_sub Hm).
elim: (m - k) => [| d Hrec]; first by rewrite subn0.
case (leqP m d) => Hd; last by apply: F; rewrite addn1 -leq_subS.
by move: (leqW Hd); rewrite /leq; move/eqP => ->; exact: ntransitive0.
Qed.

Lemma ntransitive1 m: 0 < m ->
   ntransitive to H S1 m -> transitive to H S1.
Proof.
move=> m Hm HH.
have HH1 := ntransitive_weak Hm HH.
case: HH1 => [H1 H2] x Hx y.
rewrite /ntransitive in H1.
have F1: size (Seq x) = card (setA I_(1)) by rewrite card_ordinal.
have G1: (distinctb (Fgraph F1)) by done.
have HH1: dlift S1 (EqSig _ _ G1). by rewrite /distinctb /= /setU1 Hx.
rewrite /ntransitive in H1.
move: (H1 _ HH1).
have F2: size (Seq y) = card (setA I_(1)) by rewrite card_ordinal.
have G2: (distinctb (Fgraph F2)) by done.
move/(_ (EqSig _ _ G2)).
rewrite /naction /= /f_naction.
case (S1 y).
  case/iimageP => g Hg; move/val_eqP.
  rewrite /set1 /= /set1 /= andbT; move/eqP => ->.
  apply/iimageP; exists g => //.
move/negP => HH2; apply/negP; case/iimageP => z Hz Hz1.
case: HH2; apply/iimageP; exists z => //.
apply/val_eqP => /=; rewrite /set1 /= /set1 /= andbT.
by apply/eqP.
Qed.

Lemma ntransitive_primitive: forall m,
  2 <= m -> ntransitive to H S1 m -> primitive to H S1.
Proof.
move=> m Hm Ht.
have Ht2: ntransitive to H S1 2 by apply: ntransitive_weak Ht.
apply/primitiveP => f Hf1 Hf2.
pose fP := fgraph_of_fun (fun x: S => (fgraph_of_fun (f  x))).
case E1: (forallb x: S, S1 x ==> (card (setI S1 (f x)) == 1%nat)).
  left => x y S1x S1y Hf; apply/eqP.
  move/forallP: E1; move /(_ x); move/implyP; move/(_ S1x).
  rewrite (cardD1 x) /setI Hf1 S1x // (cardD1 y) /setI /setD1 S1y Hf.
  by case: (x == _).
move/forallPn: E1; case => x.
case Hsx: (S1 x) => //=; move/idP: Hsx => Hsx HH.
have: ~ set0b(setD1 (setI S1 (f x)) x) by move: HH; rewrite (cardD1 x) /setI Hf1 Hsx.
move/negP; case/set0Pn => {HH} y; case/andP; move/eqP => Hy; case/andP => Hsy Hfy.
right => x1 y1 Hx1 Hy1.
case: Ht2 => Ht2 Hc.
case Hf3: (x1 == y1); first by rewrite (eqP Hf3) Hf1.
have F1: size (Seq y x) = card (setA I_(2)) by rewrite card_ordinal.
have G1: (distinctb (Fgraph F1)) by rewrite /distinctb /= /setU1 orbF andbT; apply/eqP.
have HH1: dlift S1 (EqSig _ _ G1) by apply/allP => z; case/or3P => //; move/eqP => <-.
have F2: size (Seq y1 x1) = card (setA I_(2)) by rewrite card_ordinal.
have G2: (distinctb (Fgraph F2)) by rewrite /distinctb /= /setU1 Hf3.
have HH2: dlift S1 (EqSig _ _ G2) by apply/allP => z; case/or3P => //; move/eqP => <-.
rewrite -(Ht2 _ HH1) in HH2; case/iimageP: HH2 => g Hg.
move/val_eqP; move/eqP; move/fgraph_eqP.
case/and3P; move/eqP => ->; move/eqP => -> _.
rewrite (Hf2 _ _ _ Hsx Hsy) // Hf1 //.
have H1: transitive to H S1 by apply: ntransitive1 Ht; apply: leq_trans Hm.
by rewrite -(H1 _ Hsy); apply/iimageP; exists g.
Qed.

Lemma trans_prim_stab: forall x, S1 x ->
  transitive to H S1 -> primitive to H S1 = maximal (group_stab to H x) H.
Proof.
move=> x Hx Ht; apply/(primitivePt Ht)/maximalP.
  move=> Hp; split; first by apply/subsetP => y; case/stabilizerP.
  move=> K Hk1 Hk2 Hk3 g; apply/idP/idP => Hg; first by apply: (subsetP Hk3).
  pose Y := image (to x) K.
  have Yx: Y x by apply/imageP; exists (1:G); [exact: group1 | rewrite act_1].
  case: (Hp Y).
  - apply/subsetP => z; case/imageP => g1 Kg1 ->.
    have Hg1: H g1 by apply: (subsetP Hk3).
    by rewrite -(Ht _ Hx); apply/iimageP; exists g1.
  - move=> g1 g2 x1 Hg1 Hg2.
    pose YY := fun z => image (fun t => to t z) Y.
    case/imageP => u1; case/imageP => g3 Kg3 -> ->.
    case/imageP => u2; case/imageP => g4 Kg4 ->; rewrite -!act_morph => Heq.
    move=> z1; apply/imageP/imageP; case => u3; case/imageP => g5 Kg5 -> ->.
      exists (to x (g5 * g1 * g2^-1)); last by rewrite -!act_morph; gsimpl.
      have ->: g5 * g1 * g2^-1 = g5 * (g3^-1 * (g3 * g1 * g2^-1 * g4^-1) * g4) by gsimpl.
      set u := _ * _; apply/imageP; exists u => //.
      rewrite groupM // groupM // ?groupV // groupM // ?groupV //.
      apply: (subsetP Hk1); apply/stabilizerP; split.
        by rewrite !groupM // ?groupV // (subsetP Hk3) //.
      by rewrite 2!act_morph Heq -!act_morph; gsimpl; rewrite act_1.
    exists (to x (g5 * g2 * g1^-1)); last by rewrite -!act_morph; gsimpl.
    have ->: g5 * g2 * g1^-1 = g5 * (g4^-1 * (g4 * g2 * g1^-1 * g3^-1) * g3) by gsimpl.
    set u := _ * _; apply/imageP; exists u => //.
    rewrite groupM // groupM // ?groupV // groupM // ?groupV //.
    apply: (subsetP Hk1); apply/stabilizerP; split.
      by rewrite !groupM // ?groupV // (subsetP Hk3) //.
    by rewrite 2!act_morph -Heq -!act_morph; gsimpl; rewrite act_1.
  - move=> HY; case: Hk2; apply/subset_eqP; rewrite Hk1; apply/subsetP => g1 Hg1.
    have F1: Y (to x g1) by apply/imageP; exists g1.
    apply/stabilizerP; split; first by apply: (subsetP Hk3).
    apply: sym_equal; apply/eqP.
    by move: HY; rewrite (cardD1 x) Yx (cardD1 (to x g1)) /setD1 F1; case: (x == _).
  move=> HH.
  have F1: S1 (to x g) by rewrite -(Ht _ Hx); apply/iimageP; exists g.
  rewrite -HH in F1; case/imageP: F1 => g1 Hg1 Hg2.
  have ->: g = (g * g1^-1) * g1 by gsimpl.
  apply: groupM => //; apply: (subsetP Hk1).
  apply/stabilizerP; split; first by rewrite groupM // groupV (subsetP Hk3).
  by rewrite act_morph Hg2 -act_morph mulgV act_1.
case => Hs Hst Y Hsub Hd.
case E1: (card Y <= 1); first by left.
right; move/idP: E1; move/idP; rewrite -(ltnNge) => E1.
have F1: ~Y =1 set0 by move => F1; move: E1; rewrite (eq_card F1) card0.
move/set0P: F1; case/set0Pn => y Hy.
have F1: ~(setD1 Y y) =1 set0.
  by move=> F1; move: E1; rewrite (cardD1 y) Hy (eq_card F1) card0.
move/set0P: F1; case/set0Pn => y1; case/andP => Hy1 Yy1.
have S1y: S1 y by apply: (subsetP Hsub).
have S1y1: S1 y1 by apply: (subsetP Hsub).
move: (Hx); rewrite -(Ht _ S1y); case/iimageP => g Hg He.
pose Y1 := image (fun z => to z g) Y.
have F1: Y1 x by apply/imageP; exists y.
have Fi: forall z, image  (fun t => to t z) Y1 =1 image  (fun t => to t (g * z)) Y.
  move=> g1 x1;apply/imageP/imageP; case => x2.
    by case/imageP => x3 Hx3 -> ->; exists x3; rewrite // act_morph.
  move=> Hx2 ->; exists (to x2 g); last by rewrite act_morph.
  by apply/imageP; exists x2.
have Hd1: wdisjointn H (fun z => image (fun t => to t z) Y1).
  move=> g1 g2 x1 Hg1 Hg2 /=; rewrite !Fi => HH HH1 z /=.
  by rewrite !Fi; apply: (Hd _ _ x1); try apply: groupM.
pose K := setI H (preimage (to x) Y1).
have F2: group_set (iset_of_fun K).
  apply/andP; split; first by rewrite s2f /K /setI /preimage act_1 group1.
  apply/subsetP => z; case/smulgP => g1 g2.
  rewrite !s2f /K /preimage; case/andP => Hg1 Yg1; case/andP => Hg2 Yg2 ->.
  apply/andP; split; first by apply: groupM.
  pose YY := fun z => image (fun t : S => to t z) Y1.
  have F2: YY 1 =1 Y1.
    move => z1; apply/imageP/idP; first  by case => z2 Hz2 ->; rewrite act_1.
    by move => Hz1; exists z1; rewrite // act_1.
  have F3: YY g2 =1 YY 1.
    apply: (@Hd1 _ _ (to x g2)) => //; first by apply/imageP; exists x.
    by apply/imageP; exists (to x g2); rewrite // act_1.
  have F4: YY (g1 * g2) =1 YY 1.
    apply: (@Hd1 _ _ (to x (g1 * g2))) => //; first by apply: groupM.
      by apply/imageP; exists x.
    rewrite /YY in F3; rewrite -F3.
    by apply/imageP; exists (to x g1); rewrite // act_morph.
  by rewrite -F2 -F4; apply/imageP; exists x.
have F3: (Group F2) =1 H.
  apply: Hst => //.
  - apply/subsetP => g1; case/stabilizerP => Hg1 Heq.
    by rewrite s2f /K /preimage /setI Hg1 /= Heq.
  - move: (Hx); rewrite -(Ht _ S1y1); case/iimageP => g1 Hg1 He1.
    move=> HH; case/negP: Hy1; apply/eqP.
    have F3: (Group F2) (g1^-1 * g).
      rewrite s2f /K /setI /preimage groupM //; last by rewrite groupV.
      rewrite He1 -!act_morph mulgA mulgV mul1g.
      by apply/imageP; exists y1.
    rewrite -HH in F3; case/stabilizerP: F3 => _ HH1.
    apply: (@inj_act _ _ to g).
    by rewrite -He -HH1 act_morph {1}He1 -!act_morph !mulgA mulgV mul1g.
  by apply/subsetP => g1 /=; rewrite s2f; case/andP.
 apply/subset_eqP; rewrite Hsub; apply/subsetP => x1 Hx1.
pose YY := fun z => image (fun t : S => to t z) Y1.
have ->: Y =1 YY g^-1.
  move=> z; rewrite /YY Fi mulgV; apply/idP/imageP.
    by move=> HH; exists z; rewrite // act_1.
  by case => x2 Hx2; rewrite act_1 => ->.
move: (Hx1); rewrite -(Ht _ Hx); case/iimageP => g1 Hg1 He1.
apply/imageP; exists (to x (g1 * g)).
  have FK: K (g1 * g) by rewrite /= in F3; rewrite -s2f F3 groupM.
  by case/andP: FK.
by rewrite -!act_morph -!mulgA mulgV mulg1.
Qed.

End NTransitveProp.

Section NTransitveProp1.


Variable (G: finGroupType) (S:finType).

Variable to : action G S.
Variable H : group G.
Variable S1: set S.

(* Correspond to => of 15.12.1 Aschbacher *)
Theorem stab_ntransitive m x:
  m >= 2 -> S1 x ->  ntransitive to H S1 m ->  
     ntransitive to (group_stab to H x) (setD1 S1 x) (m - 1).
Proof.
case => // m.
rewrite ltnS -(add1n m) subn_addr addnC => x Hlm Hs1 [Ht Hc].
have F: setU1 x (setD1 S1 x) =1 S1.
  by move => z; rewrite /setU1 /setD1; case E1: (x == z); rewrite // -(eqP E1) Hs1.
have Fm: 0 < m + 1 by rewrite addnC /=.
split; last by move: Hc; rewrite (cardD1 x) Hs1 /= addnC.
move=> x1 Lx1 y1.
have F1: ~~ dtuple_in x x1.
  move: Lx1; case: (x1) => [[xx1 Hxx1] Dxx1] HH.
  by move: (allP HH x); rewrite /setD1 eq_refl /dtuple_in /=; case (xx1 x) => //= ->.
pose x2 := dtuple_add F1; have Lx2: dlift S1 x2.
  apply: dlift_add => //; rewrite -(dlift_eq x1 F).
  by apply: dlift_sub_set Lx1; exact: setU1r.
apply/idP/idP => Ly1; last first.
  have F2: ~~ dtuple_in x y1.
    move: Ly1; case: (y1) => [[yy1 Hyy1] Dyy1] HH.
    by move: (allP HH x);
     rewrite /setD1 eq_refl /dtuple_in /=; case (yy1 x) => //= ->.
  pose (y2 := dtuple_add F2); have Ly2: dlift S1 y2.
    apply: dlift_add => //;  rewrite -(dlift_eq y1 F).
    by apply: dlift_sub_set Ly1;exact: setU1r.
  move: Ly2; rewrite /y2 -(Ht x2) //.
  case/iimageP => [a Ha] Ha'; apply/iimageP; exists a => //.
    apply/stabilizerP; split => //.
    by rewrite -{2}(dtuple_hd_add x F2) Ha' naction_hd // (dtuple_hd_add x F1).
  by rewrite -{1}(dtuple_tl_add F2) Ha' naction_tl // dtuple_tl_add.
case/iimageP: Ly1 => [a Ha] Ha'.
case/stabilizerP: Ha => Ha1 Ha2.
rewrite Ha' -{1}(dtuple_tl_add F1) -naction_tl
       -{1}Ha2 -{1}(dtuple_hd_add x F1) -naction_hd //.
by apply: dlift_tl; rewrite -(Ht x2 Lx2); apply/iimageP; exists a.
Qed.

Lemma dlift_naction: 
  forall m (x1: dtuple S m) (a1: G),
  H a1 -> transitive to H S1 ->
  dlift S1 x1 -> dlift S1 (naction to m x1 a1).
Proof.
move=> m [[[|x l] Hx] Dx] a1 Ha1 Ht //.
case/andP => Hsx; move/allP => Ha.
apply/andP; split; first by rewrite -(Ht x Hsx); apply/iimageP; exists a1.
apply/allP => x1; case/mapsP => y1 Hy1 <-.
by rewrite -(Ht y1 (Ha _ Hy1)); apply/iimageP; exists a1.
Qed.

(* Correspond to <= of 15.12.1 Aschbacher *)
Theorem stab_ntransitiveI m x:
  card S1 > m -> m >= 1 -> S1 x ->  transitive to H S1 ->
   ntransitive to (group_stab to H x) (setD1 S1 x) m ->
   ntransitive to H S1 (m + 1).
Proof.
move=> m x Hcs Hlm Hs1 Ht1 [Ht Hc].
have F: 0 < m by apply: leq_trans Hlm.
have F0: 0 < m + 1 by rewrite addnC.
split; last by rewrite addn1.
move=> x1 Hx1 y1.
pose (h1 := dtuple_hd x x1); have Sh1: S1 h1 by exact: dlift_hd.
pose (h2 := dtuple_hd x y1); move: (Hs1); rewrite -(Ht1 _ Sh1).
case/iimageP => [g1 Hg1] Hh1; apply/idP/idP => Hy1.
  by case/iimageP: Hy1 => [z Hz] ->; apply dlift_naction.
have Sh2: S1 h2 by exact: dlift_hd.
move: (Hs1); rewrite -(Ht1 _ Sh2); case/iimageP => [g2 Hg2] Hh2.
pose x2 := naction to (m + 1) x1 g1; have Hx2: x = dtuple_hd x x2 by rewrite naction_hd.
pose y2 := naction to (m + 1) y1 g2; have Hy2: x = dtuple_hd x y2  by rewrite naction_hd.
pose x3 := dtuple_tl x2; have Dx3: dlift (setD1 S1 x) x3 
  by rewrite Hx2; apply: dlift_tl; exact: dlift_naction.
pose y3 := dtuple_tl y2; have Dy3: dlift (setD1 S1 x) y3.
  by rewrite Hy2; apply: dlift_tl; exact: dlift_naction.
rewrite -(Ht _ Dx3) in Dy3; case/iimageP: Dy3 => [g3 Hg3] Hh3.
apply/iimageP; exists (g1 * g3 * g2^-1).
  by rewrite !groupM // ?groupV //; apply: (subsetP (subset_stab to H x)).
rewrite !act_morph -/x2.
suff <-: y2 = naction to (m + 1) x2 g3 by rewrite /y2 -act_morph mulgV act_1.
apply: (dtuple_hd_tl (x:=x)); last by rewrite  naction_tl.
by rewrite -Hy2 naction_hd // -Hx2; case/stabilizerP: Hg3.
Qed.

(* => of 5.20 Aschbacher *)
Theorem subgroup_transitive: 
  forall (K: group G) x, S1 x ->
   subset K H -> transitive to H S1 -> transitive to K S1 ->
    (stabilizer to H x) :*: K = H.
Proof.
move=> K x Hx H1 H2 H3.
pose H_x := stabilizer to H x.
apply/isetP => z; apply/smulgP/idP => [[hx1 k1 Hx1 Hk1 ->] | Hz].
  apply: groupM; last by apply: (subsetP H1).
  by apply (subsetP (subset_stab to H x)).
pose y := to x z; have Hy: S1 y by rewrite -(H2 x Hx); apply/iimageP; exists z.
move: (Hy); rewrite -(H3 x Hx); case/iimageP => k Hk Hk1.
exists (z * k ^-1)  k => //; last by gsimpl.
apply/stabilizerP; split; first by rewrite groupM // groupV (subsetP H1).
by rewrite act_morph -/y Hk1 -act_morph mulgV act_1.
Qed.
  
(* <= of 5.20 Aschbacher *)
Theorem subgroup_transitiveI: 
  forall (K: group G) x, S1 x ->
   subset K H -> transitive to H S1 -> 
    (stabilizer to H x) :*: K = H ->
     transitive to K S1.
Proof.
move=> K x Hx Hkh Ht Heq x1 Hx1 y1.
apply/iimageP/idP => [[g1 Hg1 ->] | Hy1].
  have F: H g1 by apply: (subsetP Hkh).
  by rewrite -(Ht _ Hx1); apply/iimageP; exists g1.
move: (Hx1); rewrite -(Ht _ Hx); case/iimageP => [g1 Hg1 Hgg1].
move: (Hg1); rewrite <- Heq; case/smulgP => h1 k1 Hh1 Hk1 Hhk1.
move: (Hy1); rewrite -(Ht _ Hx); case/iimageP => [g2 Hg2 Hgg2].
move: (Hg2); rewrite <- Heq; case/smulgP => h2 k2 Hh2 Hk2 Hhk2.
exists (k1^-1 * k2); first by rewrite groupM // groupV.
rewrite Hgg1 Hhk1 -act_morph; gsimpl; rewrite Hgg2 Hhk2 !act_morph.
by case/stabilizerP: Hh1 => _ ->; case/stabilizerP: Hh2 => _ ->.
Qed.

End NTransitveProp1.


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
