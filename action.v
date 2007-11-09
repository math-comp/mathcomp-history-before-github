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

Definition transitive (S1: set S) := 
  forall x: S, S1 x -> (to x) @: H =1 S1.

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

Section Injectiveb.

Variable d d': finType.
Variable f: d -> d'.

Definition injectivef (p: prod_finType d d) :=
match p with
| pair x y => (x != y) && (f x == f y)
end.
Definition injectiveb := (set0b injectivef).

Lemma injectiveP: (reflect (injective f) injectiveb).
Proof.
apply: (iffP idP).
  move/set0P => H x y; move/eqP => H1.
  have F1: injectivef (pair x y) = false by rewrite H.
  rewrite /injectivef H1 andbT in F1.
  by apply/eqP; move/negbEF: F1.
move => H; apply/set0P; case => x y.
rewrite /injectivef.
case E1: (f x == f y); last by rewrite andbF.
by rewrite (H x y (eqP E1)) eq_refl.
Qed.

Lemma injectiveN: ~(injective f) ->
  exists x, exists y, (x != y) && (f x == f y).
Proof.
move/injectiveP; move/set0Pn; case; case => x y H.
by exists x; exists y.
Qed.

End Injectiveb.

Section Primitive.

Variable (G: finGroupType) (S:finType).

Variable to : action G S.
Variable H : group G.

Definition primitive :=
forallb f : fgraphType S S,
if (forallb x : S,
    (forallb g : G,
     if H g then
      (card (image (fun y : S => f (to y g)) (preimage f (set1 (f x)))) ==
          1%nat)
      else true))
  then injectiveb (d:=S) (d':=S) f || (card (image f S) <= 1) else true.

Theorem primitiveP:
  reflect 
  (forall (f: S -> S),
   (forall x y g, H g -> f x = f y -> f (to x g) = f (to y g)) ->
   injective f \/ (forall x y, f x = f y))
   primitive.
Proof.
apply: (iffP idP).
  move => Hp f H1.
  move/forallP: Hp.
  move/(_ (fgraph_of_fun f)).
  case E1: (set0b _) => /=; last first.
    case/negP: E1.
    apply/forallP => x.
    apply/forallP => g.
    case H2: (H g) => //=.
    rewrite -(card1 (f (to x g))).
    apply/eqP; apply: eq_card.
    move => y.
    apply/imageP/eqP.  
      move => [z Hz1 ->].
      rewrite g2f.
      apply: H1 => //.
      rewrite /preimage !g2f in Hz1.
      by apply/eqP.
    by move => H3; exists x; rewrite /preimage !g2f //.
  clear E1; case E1: (injectiveb _) => //=.
    move => _; left.
    move/injectiveP: E1 => E1 x y Hx.
    apply: E1.
    by rewrite !g2f.
  move => H2; right.
  move => x y.
  set f1 := fgraph_of_fun _ in H2.
  have F1: card (setD1 (image f1 S) (f1 x)) <= 0.
    rewrite -(leq_add2l 1).
    by move: H2; rewrite (cardD1 (f1 x)) image_f_imp.
  case E2: (f x == f y).
    by apply/eqP.
  move: F1; rewrite (cardD1 (f1 y)).
  by rewrite /setD1 image_f_imp // !g2f E2.
move => H1.
apply/forallP => f.
case E0: (set0b _) => //=.
case E1: (injectiveb _) => //=.
case: (H1 f).
    move => x y g Hg Hf.
    move/forallP: E0; move /(_ x).
    move/forallP; move /(_ g).
    rewrite Hg /=.
    rewrite /preimage (cardD1 (f (to x g))) image_f_imp //.
    rewrite (cardD1 (f (to y g))) /setD1 image_f_imp ?Hf //.
    case E2: (_ != _) => //.
    by move/negPn: E2; move/eqP.
  by move => H2; move/injectiveP: E1.
move => H2.
case E2: (card S == 0).
  apply: (leq_trans (leq_image_card _ _)).
  by rewrite (eqP E2).
case: (pickP S) => [x|] Hx; last first.
  apply: (leq_trans (leq_image_card _ _)).
  suff ->: card S = 0 by done.
  by rewrite (eq_card Hx) card0.
suff ->: card (image f S) = 1%nat by done.
rewrite -(card1 (f x)).
apply: eq_card => y.
apply/imageP/idP.
  by move => [z _ ->]; rewrite (H2 x z).
by move/eqP => Hy; exists x.
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
move => x y [[z Hz] Dz].
rewrite /f_naction; apply/val_eqP => /=.
rewrite /set1 /=; apply/eqseqP.
rewrite -maps_comp.
apply: eq_maps => t.
exact: act_morph.
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
by move => S n [[x Hx] Dx]; apply/allP.
Qed.

Lemma dlift_sub_set:
forall m (S: finType) (S1 S2: set S),
 sub_set S1 S2 -> sub_set (dlift (n := m) S1) (dlift (n := m) S2).
Proof.
move => m S S1 S2 H [[x Hx] Hx1] /= H1.
apply/allP => z Hz.
apply: (H z).
by apply: (allP H1 z).
Qed.

Lemma dlift_eq: forall m (S: finType) (S1 S2: set S)
                        (t: dtuple S m),
  S1 =1 S2 -> (dlift S1 t) = dlift S2 t.
by move => m S S1 S2 t H; apply/idP/idP => H1;
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
move => S m [[x Hx] Dx] /=.
by move: (Hx); rewrite card_ordinal.
Qed.

Lemma dtuple_get_card (S: finType) m (t: dtuple S m): 
 card (dtuple_get t) = m.
Proof.
move => S m [[x Hx] Dx] /=.
move: (Hx); rewrite card_ordinal.
by move => <-; apply/card_uniqP.
Qed.

Lemma dtuple_get_sub_set (S: finType) (S1: set S) m (t: dtuple S m): 
 dlift S1 t -> sub_set (dtuple_get t) S1.
Proof.
move => S S1 m [[x Hx] Dx] /= H1 x1 Hx1.
exact: (allP H1).
Qed.

Let dtuple_add_aux: forall m (S: finType) x (x1: seq S),
  size x1 = card (setA I_(m)) ->
  size (Adds x x1) = card (setA I_(m + 1)).
move => m S x x1 Hx1.
by rewrite card_ordinal addnC -(card_ordinal m) -Hx1.
Qed.

Definition dtuple_add (S: finType) m (x:S) (t: dtuple S m):
    ~~(dtuple_in x t) -> dtuple S (m + 1).
intros S m x [[x1 Hx1] Dx1] => /= H.
exists (Fgraph (dtuple_add_aux x Hx1)).
by rewrite /distinctb /= H.
Defined.

Definition dtuple_hd S m s (t: dtuple S m) := head s (dtuple_get t).

Lemma dtuple_hd_add (S: finType) m (x y:S) (t: dtuple S m) 
         (F: ~~(dtuple_in x t)):
  dtuple_hd y (dtuple_add F) = x.
Proof.
by move => S m x y [[xx Hxx] Dx].
Qed.

Let dtuple_tl_aux: forall m (S: finType) (x1: seq S),
  size x1 = card (setA I_(m + 1)) ->
  size (behead x1) = card (setA I_(m)).
move => m S [| x1 l] /=.
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
move => S m x [[xx Hxx] Dx] F; apply/val_eqP.
by rewrite /set1 /=.
Qed.

Lemma dtuple_hd_tl (S: finType) m (x:S) (t1 t2: dtuple S (m + 1)):
  dtuple_hd x t1 = dtuple_hd x t2 ->
  dtuple_tl t1 = dtuple_tl t2 ->
  t1 = t2.
Proof.
move => S m x [[[|t1 l1] Ht1] Dt1].
  by apply False_ind; move: (Ht1); rewrite /= card_ordinal addnC.
move => [[[|t2 l2] Ht2] Dt2].
  by apply False_ind; move: (Ht2); rewrite /= card_ordinal addnC.
rewrite /dtuple_hd /= => H1.
move/val_eqP; rewrite /set1 /= => H2.
apply/val_eqP; rewrite /set1 /= /set1 /=.
by rewrite H1 eqseqE H2 eq_refl.
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
move => m S S1 a1 [[[| x l] Hx] Dx] //=.
  apply False_ind; move: (Hx) => /=; 
  by rewrite card_ordinal addnC.
by case/andP.
Qed.

Lemma dlift_tl:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S (m + 1)),
 dlift S1 x ->
 dlift (setD1 S1 (dtuple_hd a1 x)) (dtuple_tl x).
Proof.
move => m S S1 a1 [[[| x l] Hx] Dx] //=.
rewrite /dlift /dtuple_tl /dtuple_hd /=.
move: Dx; rewrite /distinctb /=; case/andP => Dx Dx1.
case/andP => Dx2; move/allP => Dx3.
apply/allP => z Hz.
rewrite /setD1 Dx3 ?Hz // andbT.
elim: (l) Dx Dx1 Hz => //= a l1 Hrec H1; move/andP => [H2 H3].
case/orP => [| HH].
  move/eqP => <-; apply/negP => HH; case/negP: H1.
  by rewrite (eqP HH) setU11.
apply: Hrec => //.
apply/negP => HH1; case/negP: H1.
by rewrite/setU1 HH1 orbT.
Qed.

Lemma dlift_tlw:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S (m + 1)),
 dlift S1 x -> dlift S1 (dtuple_tl x).
Proof.
move => m S S1 a1 x H.
have F := dlift_tl a1 H.
apply: dlift_sub_set F => z.
by case/andP.
Qed.

Lemma dlift_add_gen:
forall m (S: finType) (S1: set S) (a1: S) (x: dtuple S m)
(F1 : ~~ dtuple_in a1 x),
 dlift S1 x -> dlift (setU1 a1 S1) (dtuple_add F1).
Proof.
move => m S S1 a1 [[x Hx] Dx] /=.
rewrite setU11 /= => H.
move/allP => H1; apply/allP => xx Hxx.
by rewrite /setU1 H1 // orbT.
Qed.

Lemma naction_hd:
forall m (G: finGroupType) 
  (S: finType) a (a1: S) (to: action G S) (x: dtuple S m),
 0 < m -> dtuple_hd a1 (naction to m x a) = to (dtuple_hd a1 x) a.
Proof.
move => m G S a a1 xto [[[|x l] Hx] Dx];
 rewrite /dtuple_hd //=.
by move: (Hx); rewrite card_ordinal /= => <-.
Qed.

Lemma naction_tl:
forall m (G: finGroupType)
  (S: finType) a (to: action G S) (x: dtuple S (m + 1)),
 dtuple_tl (naction to (m + 1) x a) = naction to m (dtuple_tl x) a.
Proof.
move => m G S a xto [[x Hx] Dx];
 rewrite /dtuple_tl //=.
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
apply/idP/idP => H1.
  by case: (y) => [[[|yy ll] Hyy] Dyy].
apply/iimageP; exists (1:G) => //=.
case: (x) => [[[|xx ll] Hxx]  Dxx] => //=.
case: (y) => [[[|yy ll] Hyy] Dyy] => //=.
by apply/val_eqP.
Qed.

Lemma ntransitive_weak: forall k m,
k <= m -> ntransitive to H S1 m-> ntransitive to H S1 k.
Proof.
assert (F: forall m, ntransitive to H S1 (m + 1) -> ntransitive to H S1 m).
  move => m [H1 H2]; split; rewrite addnC in H2; last first.
    by apply: leq_trans H2; rewrite leqnSn.
  move => x Hx y.
  set x1 := dtuple_get x.
  have F: ~~ set0b  (setI S1 (setC x1)).
    rewrite /set0b.
    apply/negP => HH.
    move: H2; rewrite -(cardIC x1) (eqP HH) addn0.
    replace (card (setI S1 x1)) with (card x1).
      by rewrite /x1 dtuple_get_card add1n ltnn.
    apply: eq_card => z; rewrite /setI.
    move: (@dtuple_get_sub_set S S1 m x Hx z).
    by rewrite -/x1; case (x1 z); case (S1 z) => // ->.
  case/set0Pn: F => a1; case/andP => Ha1 Hb1.
  have F1: ~~ dtuple_in a1 x.
    move: Hb1; rewrite /x1.
    by case: (x) => [[xx Hxx] Dxx].
  set (x2 := dtuple_add F1).
  set y1 := dtuple_get y.
  apply/idP/idP => Hy; last first.
    have F: ~~ set0b  (setI S1 (setC y1)).
      rewrite /set0b.
      apply/negP => HH.
      move: H2; rewrite -(cardIC y1) (eqP HH) addn0.
      replace (card (setI S1 y1)) with (card y1).
        by rewrite /x1 dtuple_get_card add1n ltnn.
      apply: eq_card => z; rewrite /setI.
      move: (@dtuple_get_sub_set S S1 m y Hy z).
      by rewrite -/y1; case (y1 z); case (S1 z) => // ->.
    case/set0Pn: F => a2; case/andP => Ha2 Hb2.
    have F2: ~~ dtuple_in a2 y.
      move: Hb2; rewrite /y1.
      by case: (y) => [[yy Hyy] Dyy].
    set (y2 := dtuple_add F2).
    have DLx2: dlift S1 x2.
      by apply: dlift_add.
    have DLy2: dlift S1 y2.
      by apply: dlift_add.
    move: (H1 _ DLx2 y2); rewrite DLy2.
    move/iimageP => [a Ha] Ha'.
    apply/iimageP; exists a => //.
    rewrite /y2 /x2 in Ha'.
    by rewrite -(dtuple_tl_add F2) Ha' naction_tl
               dtuple_tl_add.
  case/iimageP: Hy => a Ha Hya.
  have DLx2: dlift S1 x2.
    rewrite /x2; apply dlift_add => //.
  set z := naction to (m + 1) x2 a.
  replace y with (dtuple_tl z);
    last by rewrite /z Hya /x2 naction_tl dtuple_tl_add.
  apply: dlift_tlw => //.
  rewrite /z -(H1 x2) //.
  by apply/iimageP; exists a.
move => k m Hm Ht.
rewrite -(leq_sub_sub Hm).
elim: (m - k) => [| d Hrec].
  by rewrite subn0.
case (leqP m d) => Hd.
  move: (leqW Hd); rewrite /leq.
  by move/eqP => ->; exact: ntransitive0.
apply: F.
by rewrite addn1 -leq_subS.
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
  move => z; rewrite /setU1 /setD1.
  case E1: (x == z) => //.
  by rewrite -(eqP E1) Hs1.
have Fm: 0 < m + 1 by rewrite addnC /=.
split; last first.
  by move: Hc; rewrite (cardD1 x) Hs1 /= addnC.
move => x1 Lx1 y1.
have F1: ~~ dtuple_in x x1.
  move: Lx1.
  case: (x1) => [[xx1 Hxx1] Dxx1] /= HH.
  by move: (allP HH x);
     rewrite /setD1 eq_refl /dtuple_in /=;
     case (xx1 x) => //= ->.
set (x2 := dtuple_add F1).
have Lx2: dlift S1 x2.
  apply: dlift_add => //.
  rewrite -(dlift_eq x1 F).
  apply: dlift_sub_set Lx1.
  by exact: setU1r.
apply/idP/idP => Ly1; last first.
  have F2: ~~ dtuple_in x y1.
    move: Ly1.
    case: (y1) => [[yy1 Hyy1] Dyy1] /= HH.
    by move: (allP HH x);
     rewrite /setD1 eq_refl /dtuple_in /=; case (yy1 x) => //= ->.
  set (y2 := dtuple_add F2).
  have Ly2: dlift S1 y2.
    apply: dlift_add => //.
    rewrite -(dlift_eq y1 F).
    apply: dlift_sub_set Ly1.
    by exact: setU1r.
  move: Ly2; rewrite /y2.
  rewrite -(Ht x2) //.
  case/iimageP => [a Ha] Ha'.
  apply/iimageP; exists a => //.
    apply/stabilizerP; split => //.
    assert (FF: 0 < m + 1) by rewrite addnC //.
    by rewrite -{2}(dtuple_hd_add x F2) Ha' naction_hd //
            (dtuple_hd_add x F1).
  by rewrite -{1}(dtuple_tl_add F2) Ha' naction_tl //
            dtuple_tl_add.
case/iimageP: Ly1 => [a Ha] Ha'.
case/stabilizerP: Ha => Ha1 Ha2.
rewrite Ha' -{1}(dtuple_tl_add F1) -naction_tl
       -{1}Ha2 -{1}(dtuple_hd_add x F1) -naction_hd //.
apply: dlift_tl.
rewrite -(Ht x2 Lx2).
by apply/iimageP; exists a.
Qed.

Lemma dlift_naction: 
  forall m (x1: dtuple S m) (a1: G),
  H a1 -> transitive to H S1 ->
  dlift S1 x1 -> dlift S1 (naction to m x1 a1).
Proof.
move => m [[[|x l] Hx] Dx] a1 Ha1 Ht //=.
case/andP => Hsx; move/allP => Ha.
apply/andP; split.
  rewrite -(Ht x Hsx).
  by apply/iimageP; exists a1.
apply/allP => x1.
case/mapsP => y1 Hy1 <-.
rewrite -(Ht y1 (Ha _ Hy1)).
by apply/iimageP; exists a1.
Qed.

(* Correspond to <= of 15.12.1 Aschbacher *)
Theorem stab_ntransitiveI m x:
  card S1 > m -> m >= 1 -> S1 x ->  transitive to H S1 ->
   ntransitive to (group_stab to H x) (setD1 S1 x) m ->
   ntransitive to H S1 (m + 1).
Proof.
move =>  m x Hcs Hlm Hs1 Ht1 [Ht Hc].
have F: 0 < m   by apply: leq_trans Hlm.
have F0: 0 < m + 1   by rewrite addnC.
split; last by rewrite addn1.
move => x1 Hx1 y1.
set (h1 := dtuple_hd x x1).
have Sh1: S1 h1 by exact: dlift_hd.
set (h2 := dtuple_hd x y1).
move: (Hs1); rewrite -(Ht1 _ Sh1).
case/iimageP => [g1 Hg1] Hh1.
apply/idP/idP => Hy1.
  case/iimageP: Hy1 => [z Hz] ->.
  by apply dlift_naction.
have Sh2: S1 h2 by exact: dlift_hd.
move: (Hs1); rewrite -(Ht1 _ Sh2).
case/iimageP => [g2 Hg2] Hh2.
set x2 := naction to (m + 1) x1 g1.
have Hx2: x = dtuple_hd x x2 by rewrite naction_hd.
set y2 := naction to (m + 1) y1 g2.
have Hy2: x = dtuple_hd x y2  by rewrite naction_hd.
set x3 := dtuple_tl x2.
set y3 := dtuple_tl y2.
have Dx3: dlift (setD1 S1 x) x3.
  rewrite Hx2; apply: dlift_tl.
  by exact: dlift_naction.
have Dy3: dlift (setD1 S1 x) y3.
  rewrite Hy2; apply: dlift_tl.
  by exact: dlift_naction.
rewrite -(Ht _ Dx3) in Dy3.
case/iimageP: Dy3 => [g3 Hg3] Hh3.
apply/iimageP; exists (g1 * g3 * g2^-1).
  rewrite !groupM // ?groupV //.
  by apply: (subsetP (subset_stab to H x)).
rewrite !act_morph -/x2.
have <-: y2 = naction to (m + 1) x2 g3.
  apply: (dtuple_hd_tl (x:=x)).
    rewrite -Hy2 naction_hd // -Hx2.
    by case/stabilizerP: Hg3.
  by rewrite  naction_tl.
by rewrite /y2 -act_morph mulgV act_1.
Qed.

(* => of 5.20 Aschbacher *)
Theorem subgroup_transitive: 
  forall (K: group G) (x:S), S1 x ->
   subset K H -> transitive to H S1 -> transitive to K S1 ->
    (stabilizer to H x) :*: K = H.
Proof.
move => K x Hx H1 H2 H3.
set H_x := stabilizer to H x.
apply/isetP => z; apply/smulgP/idP => [[hx1 k1 Hx1 Hk1 ->] | Hz].
  apply: groupM; last by apply: (subsetP H1).
  by apply (subsetP (subset_stab to H x)).
set y := to x z.
have Hy: S1 y.
  rewrite -(H2 x Hx).
  by apply/iimageP; exists z.
move: (Hy); rewrite -(H3 x Hx).
case/iimageP => k Hk Hk1.
exists (z * k ^-1)  k => //.
  apply/stabilizerP; split.
    by rewrite groupM // groupV (subsetP H1).
  by rewrite act_morph -/y Hk1 -act_morph mulgV act_1.
by gsimpl.
Qed.
  

(* <= of 5.20 Aschbacher *)
Theorem subgroup_transitiveI: 
  forall (K: group G) (x:S), S1 x ->
   subset K H -> transitive to H S1 -> 
    (stabilizer to H x) :*: K = H ->
     transitive to K S1.
Proof.
move => K x Hx Hkh Ht Heq x1 Hx1 y1.
apply/iimageP/idP => [[g1 Hg1 ->] | Hy1].
  have F: H g1 by apply: (subsetP Hkh).
  rewrite -(Ht _ Hx1).
  by apply/iimageP; exists g1.
move: (Hx1); rewrite -(Ht _ Hx).
case/iimageP => [g1 Hg1 Hgg1].
move: (Hg1); rewrite <- Heq.
case/smulgP => h1 k1 Hh1 Hk1 Hhk1.
move: (Hy1); rewrite -(Ht _ Hx).
case/iimageP => [g2 Hg2 Hgg2].
move: (Hg2); rewrite <- Heq.
case/smulgP => h2 k2 Hh2 Hk2 Hhk2.
exists (k1^-1 * k2).
  by rewrite groupM // groupV.
rewrite Hgg1 Hhk1 -act_morph; gsimpl.
rewrite Hgg2 Hhk2 !act_morph.
case/stabilizerP: Hh1 => _ ->.
by case/stabilizerP: Hh2 => _ ->.
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
